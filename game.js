// 完整玩法移植 —— 与 Python 版 game_survivor.py 同一套数值
// 6 武器 / 6 敌人 / 经验升级 / 4 被动 / 双角色轮流控制 / 认知训练层
//
// 与 camera 解耦：外部每帧调用 game.update(dt, hand)，hand 为
// { palm:{x,y}, openness } 或 null（坐标已归一化到 0~1）。

export const W = 960, H = 700, HUD = 46;
export const PLAY_T = HUD, PLAY_B = H;
const PW = W, PH = PLAY_B - PLAY_T;

// ------------------------------------------------ 常量（对齐 Python 版）
const PLAYER_R = 13;
const PLAYER_SPEED = 300;
const JOY_HALF = 0.16, JOY_DEAD = 0.06;
const SURVIVE_SEC = 160;
const START_HP = 120, HIT_DAMAGE = 5, INVULN = 0.9;
const MAX_SLOTS = 3;

const FIRST_SWITCH = 15, SWITCH_EVERY = 12;
const CTRL_SWITCH = 20, CTRL_PREP = 8, PREP_SEC = 8;
const TARGET_R = 42, TARGET_TIMEOUT = 12, TARGET_GAP = 5;

const MAX_ENEMIES = 150, MAX_BULLETS = 200, MAX_GEMS = 120;

export const C = {
  bg: "#14161b", grid: "#1e2129", text: "#eceef2", dim: "#7c828c",
  good: "#6edc8c", warn: "#f0a050", bad: "#e05a5a",
  player: "#fff6d6", player2: "#ffaa6e", target: "#78ffc8",
  orb: "#78aaff", aura: "#78aaff", nova: "#c8a6ff", xp: "#6ee0ff",
  enemy: "#5a82f0", runner: "#46c8e6", tank: "#be64dc",
  elite: "#f0c85a", boss: "#e04a6a", split: "#7ad07a",
};

const clamp = (v, a, b) => v < a ? a : (v > b ? b : v);
const rnd = (a, b) => a + Math.random() * (b - a);

// ------------------------------------------------ 武器定义
export const WEAPONS = {
  BOLT: { name: "BOLT", max: 5, desc: "single fast shot", color: "#9fd8ff" },
  FAN: { name: "FAN", max: 5, desc: "multi-pellet spread", color: "#8fd6a0" },
  CHAIN: { name: "CHAIN", max: 5, desc: "lightning that jumps", color: "#c8b6ff" },
  ORB: { name: "ORB", max: 5, desc: "orbs orbiting you", color: "#78aaff" },
  AURA: { name: "AURA", max: 5, desc: "damages all nearby", color: "#7ac8e0" },
  NOVA: { name: "NOVA", max: 5, desc: "periodic burst + push", color: "#c8a6ff" },
};

export const PASSIVES = {
  SPEED: { name: "SWIFT", max: 5, desc: "+10% move speed" },
  VITAL: { name: "VITAL", max: 5, desc: "+20 max HP" },
  MAGNET: { name: "MAGNET", max: 5, desc: "+30% pickup range" },
  POWER: { name: "POWER", max: 5, desc: "+12% all damage" },
};

// ------------------------------------------------ 小工具
function joyAxis(v, center) {
  let n = clamp((v - center) / JOY_HALF, -1, 1);
  if (Math.abs(n) < JOY_DEAD) return 0;
  const s = n > 0 ? 1 : -1;
  return s * (Math.abs(n) - JOY_DEAD) / (1 - JOY_DEAD);
}

export class Game {
  constructor(dual) {
    this.dual = !!dual;
    this.reset();
  }

  reset() {
    this.t = 0; this.over = false; this.won = false;
    this.p1 = this.makePlayer(PW * 0.34, PH * 0.58);
    this.p2 = this.makePlayer(PW * 0.70, PH * 0.42);
    // 起始武器：随机一把，让每一局的构筑不同（没有武器会被怪堆死）
    const keys = Object.keys(WEAPONS);
    const startKey = keys[Math.floor(Math.random() * keys.length)];
    this.p1.weapons[startKey] = 1;
    this.p2.weapons[startKey] = 1;
    this.startKey = startKey;
    this.active = 0;
    this.ctrlT = 0; this.ctrlPrep = 0;
    this.prep = PREP_SEC;

    this.reach = { lo: null, hi: null, t0: null, cx: null, cy: null };
    this.joy = { x: 0, y: 0 };
    this.calibrating = true;

    this.reverse = false; this.nextSwitch = FIRST_SWITCH; this.warnSwitch = false;
    this.target = null; this.targetGap = 0;
    this.hits = 0; this.spawned = 0; this.hitTimes = []; this.switchErr = 0;
    this.errWindow = false; this.errCounted = false;
    this.lastP = { x: this.p1.x, y: this.p1.y };

    this.enemies = []; this.bullets = []; this.gems = []; this.marks = [];
    this.floats = []; this.beams = [];
    this.spawnT = 0; this.lull = 0; this.nextLull = 34;
    this.bossSpawned = false;

    this.levelup = null;   // { choices:[{key,kind,lv}], since }
    this.mode = "play";    // play | levelup | end
    this.stats = { kills: 0 };
    this.particles = [];
    this.hintOn = true;
  }

  makePlayer(x, y) {
    return {
      x, y, face: -Math.PI / 2, hp: START_HP, maxHp: START_HP,
      inv: 0, xp: 0, level: 1, need: 6,
      weapons: {}, passives: {},
      boltT: 0, fanT: 0, chainT: 0, novaT: 3, orbA: 0,
    };
  }

  // ---------------------------------------------- 组卡
  buildChoices(p) {
    const pool = [];
    for (const k of Object.keys(p.weapons)) {
      if (p.weapons[k] < WEAPONS[k].max) pool.push({ key: k, kind: "weapon" });
    }
    if (Object.keys(p.weapons).length < MAX_SLOTS) {
      for (const k of Object.keys(WEAPONS)) {
        if (!(k in p.weapons)) pool.push({ key: k, kind: "new" });
      }
    }
    for (const k of Object.keys(p.passives)) {
      if (p.passives[k] < PASSIVES[k].max) pool.push({ key: k, kind: "passive" });
    }
    if (Object.keys(p.passives).length < 4) {
      for (const k of Object.keys(PASSIVES)) {
        if (!(k in p.passives)) pool.push({ key: k, kind: "passiveNew" });
      }
    }
    // 洗牌取两张
    for (let i = pool.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [pool[i], pool[j]] = [pool[j], pool[i]];
    }
    const out = [];
    const seen = new Set();
    for (const c of pool) {
      if (seen.has(c.key)) continue;
      seen.add(c.key);
      out.push(c);
      if (out.length === 2) break;
    }
    return out;
  }

  openLevelup(p) {
    this.mode = "levelup";
    this.levelup = { choices: this.buildChoices(p), owner: p, side: 0, hold: 0, since: 0 };
  }

  applyChoice(c, p) {
    const lv = (c.kind === "passive" || c.kind === "passiveNew")
      ? (p.passives[c.key] || 0) + 1
      : (p.weapons[c.key] || 0) + 1;
    if (c.kind === "passive" || c.kind === "passiveNew") {
      p.passives[c.key] = lv;
      if (c.key === "VITAL") { p.maxHp += 20; p.hp += 20; }
    } else {
      p.weapons[c.key] = lv;
    }
    this.mode = "play";
    this.levelup = null;
    p.inv = Math.max(p.inv, INVULN);
  }

  // ---------------------------------------------- 主更新
  update(dt, hand) {
    if (this.prep > 0) {
      this.prep = Math.max(0, this.prep - dt);
      this.calibrating = true;
      if (hand) this.learnReach(hand, dt, true);
      return;
    }
    if (this.ctrlPrep > 0) {
      this.ctrlPrep = Math.max(0, this.ctrlPrep - dt);
      return;
    }
    if (this.mode === "levelup") { this.updateLevelup(dt, hand); return; }
    if (this.over) return;

    this.t += dt;
    const act = this.activePlayer();
    this.p1.inv = Math.max(0, this.p1.inv - dt);
    this.p2.inv = Math.max(0, this.p2.inv - dt);

    this.applyJoystick(hand, dt);
    this.updateTimers(dt);
    this.updateTargets(dt);
    this.updateSpawning(dt);
    this.updateWeapons(dt, this.p1);
    if (this.dual) this.updateWeapons(dt, this.p2);
    this.updateGems(dt);
    this.updateEnemies(dt);
    this.updateGems(dt, act);
    this.updateFx(dt);

    if (this.p1.hp <= 0 || (this.dual && this.p2.hp <= 0)) {
      this.over = true; this.won = false; this.mode = "end";
    }
    if (this.t >= SURVIVE_SEC) {
      this.over = true; this.won = true; this.mode = "end";
    }
  }

  activePlayer() { return this.dual && this.active === 1 ? this.p2 : this.p1; }

  learnReach(hand, dt, isPrep) {
    const R = this.reach, x = hand.palm.x;
    if (R.lo === null) {
      R.lo = R.hi = x; R.t0 = this.t; R.cx = x; R.cy = hand.palm.y;
      return;
    }
    R.lo = Math.min(R.lo, x);
    R.hi = Math.max(R.hi, x);
    if (isPrep || this.calibrating) {
      R.cx = (R.lo + R.hi) / 2;
      R.cy = hand.palm.y;
    }
    if (R.t0 !== null && this.t - R.t0 > 8) this.calibrating = false;
  }

  recenter(hand) {
    if (!hand) return;
    this.reach.cx = hand.palm.x;
    this.reach.cy = hand.palm.y;
  }

  applyJoystick(hand, dt) {
    if (!hand) { this.joy.x = 0; this.joy.y = 0; return; }
    this.learnReach(hand, dt, false);
    let jx = joyAxis(hand.palm.x, this.reach.cx);
    let jy = joyAxis(hand.palm.y, this.reach.cy);
    if (this.reverse) { jx = -jx; jy = -jy; }
    this.joy.x = jx; this.joy.y = jy;

    const mag = Math.hypot(jx, jy);
    if (mag > 1e-6) {
      const ux = jx / mag, uy = jy / mag;
      const p = this.activePlayer();
      const sp = PLAYER_SPEED * Math.pow(Math.min(1, mag), 0.6)
                 * (1 + 0.10 * (p.passives.SPEED || 0));
      p.face = Math.atan2(uy, ux);
      p.x += ux * sp * dt;
      p.y += uy * sp * dt;
    }
    for (const p of [this.p1, this.p2]) {
      p.x = clamp(p.x, PLAYER_R, PW - PLAYER_R);
      p.y = clamp(p.y, PLAYER_R, PH - PLAYER_R);
    }
  }

  updateTimers(dt) {
    if (this.dual) {
      this.ctrlT += dt;
      if (this.ctrlT >= CTRL_SWITCH) {
        this.ctrlT = 0;
        this.active = 1 - this.active;
        this.ctrlPrep = CTRL_PREP;
        const p = this.activePlayer();
        this.floats.push({ x: p.x, y: p.y - 46, txt: this.active ? "P2 CTRL" : "P1 CTRL",
                           life: 1.2, col: this.active ? C.player2 : C.player });
      }
    }
    if (this.t >= this.nextSwitch) {
      this.reverse = !this.reverse;
      this.nextSwitch += SWITCH_EVERY;
      this.errWindow = true; this.errCounted = false;
      this.switchT = this.t;
      const p = this.activePlayer();
      this.floats.push({ x: p.x, y: p.y - 46, txt: this.reverse ? "REVERSE" : "NORMAL",
                         life: 1.2, col: this.reverse ? C.warn : C.good });
    }
    this.warnSwitch = (this.nextSwitch - this.t) <= 1.5;
    if (this.lull <= 0 && this.t >= this.nextLull) { this.lull = 6; this.nextLull += 34; }
    this.lull = Math.max(0, this.lull - dt);
  }

  updateTargets(dt) {
    if (!this.target) {
      if (this.targetGap > 0) this.targetGap = Math.max(0, this.targetGap - dt);
      else this.spawnTarget();
      return;
    }
    const ps = this.dual ? [this.p1, this.p2] : [this.p1];
    const hit = ps.some(p => Math.hypot(this.target.x - p.x, this.target.y - p.y)
                             < TARGET_R + PLAYER_R);
    if (hit) {
      this.hits++;
      this.hitTimes.push(this.t - this.target.born);
      this.burst(this.target.x, this.target.y, C.target, 14, 200);
      this.target = null; this.targetGap = TARGET_GAP;
    } else if (this.t - this.target.born > TARGET_TIMEOUT) {
      this.target = null; this.targetGap = TARGET_GAP;
    }
  }

  spawnTarget() {
    const p = this.activePlayer();
    for (let i = 0; i < 26; i++) {
      const x = 80 + Math.random() * (PW - 160);
      const y = 90 + Math.random() * (PH - 170);
      if (Math.hypot(x - p.x, y - p.y) > 180) {
        this.target = { x, y, born: this.t };
        this.spawned++;
        return;
      }
    }
    this.target = { x: PW / 2, y: PH / 2, born: this.t };
    this.spawned++;
  }

  // 抑制失败判定：反转后 1.2 秒内，位移方向与目标方向相反
  updateErrWindow() {
    const p = this.activePlayer();
    const dx = p.x - this.lastP.x, dy = p.y - this.lastP.y;
    this.lastP = { x: p.x, y: p.y };
    if (!this.errWindow) return;
    if (this.t - (this.switchT || 0) > 1.2) { this.errWindow = false; return; }
    if (this.errCounted || !this.target) return;
    if (dx * dx + dy * dy < 4) return;
    const tx = this.target.x - p.x, ty = this.target.y - p.y;
    if (dx * tx + dy * ty < 0) { this.switchErr++; this.errCounted = true; }
  }

  updateSpawning(dt) {
    const k = this.t / SURVIVE_SEC;
    if (!this.bossSpawned && this.t >= 140) {
      this.bossSpawned = true;
      this.enemies.push({ kind: "boss", x: PW / 2, y: PLAY_T + 40,
                          hp: 150, maxHp: 150, spd: 78, r: 30, dmg: 12, xp: 40 });
    }
    if (this.lull > 0) return;
    if (this.enemies.length >= MAX_ENEMIES) return;
    this.spawnT -= dt;
    if (this.spawnT > 0) return;
    this.spawnT = Math.max(0.22, 0.58 - 0.30 * k);
    const n = Math.random() < 0.55 + 0.45 * k ? 2 : 1;
    for (let i = 0; i < n && this.enemies.length < MAX_ENEMIES; i++) this.spawnEnemy(k);
  }

  spawnEnemy(k) {
    const roll = Math.random();
    let kind = "grunt";
    if (roll > 0.86) kind = "elite";
    else if (roll > 0.66) kind = "tank";
    else if (roll > 0.42) kind = "runner";
    else if (roll > 0.30) kind = "splitter";

    const side = Math.floor(Math.random() * 4);
    let x, y;
    if (side === 0) { x = Math.random() * PW; y = PLAY_T - 18; }
    else if (side === 1) { x = Math.random() * PW; y = PLAY_B + 18; }
    else if (side === 2) { x = -18; y = PLAY_T + Math.random() * PH; }
    else { x = PW + 18; y = PLAY_T + Math.random() * PH; }

    const base = {
      grunt: { hp: 1.0, spd: 52, r: 10, dmg: 5, xp: 1, col: C.enemy },
      runner: { hp: 0.6, spd: 92, r: 8, dmg: 4, xp: 1, col: C.runner },
      tank: { hp: 3.4, spd: 36, r: 16, dmg: 8, xp: 3, col: C.tank },
      splitter: { hp: 1.5, spd: 58, r: 12, dmg: 5, xp: 2, col: C.split },
      elite: { hp: 4.0, spd: 54, r: 17, dmg: 9, xp: 6, col: C.elite },
    }[kind];
    const s = 1 + 2.0 * k;
    this.enemies.push({
      kind, x, y,
      hp: base.hp * s * rnd(0.85, 1.15), maxHp: base.hp * s,
      spd: base.spd * (1 + 0.35 * k), r: base.r, dmg: base.dmg,
      xp: base.xp, col: base.col,
    });
  }

  // ---------------------------------------------- 武器
  updateWeapons(dt, p) {
    const power = 1 + 0.12 * (p.passives.POWER || 0);

    if (p.weapons.BOLT) {
      const lv = p.weapons.BOLT;
      p.boltT -= dt;
      if (p.boltT <= 0) {
        p.boltT = Math.max(0.18, 0.60 - 0.07 * lv);
        const e = this.nearestEnemy(p.x, p.y, 620);
        if (e) this.fire(p, e, 0.9 + 0.6 * lv, power, 640, "bolt");
      }
    }
    if (p.weapons.FAN) {
      const lv = p.weapons.FAN;
      p.fanT -= dt;
      if (p.fanT <= 0) {
        p.fanT = 0.95;
        const n = 2 + lv;
        const targets = this.nearestEnemies(p.x, p.y, 520, n);
        if (targets.length) {
          for (const e of targets) this.fire(p, e, 0.8 + 0.30 * lv, power, 560, "fan");
        } else {
          const a0 = p.face - 0.25 * n;
          for (let i = 0; i < n; i++) {
            const a = a0 + 0.5 * i;
            this.bullets.push({ x: p.x, y: p.y, vx: Math.cos(a) * 560, vy: Math.sin(a) * 560,
              dmg: (0.8 + 0.30 * lv) * power, r: 4, life: 1.1, col: "#8fd6a0", pierce: 0 });
          }
        }
      }
    }
    if (p.weapons.CHAIN) {
      const lv = p.weapons.CHAIN;
      p.chainT -= dt;
      if (p.chainT <= 0) {
        p.chainT = 1.5;
        const first = this.nearestEnemy(p.x, p.y, 460);
        if (first) {
          let cur = first, from = { x: p.x, y: p.y };
          const hitSet = new Set();
          const jumps = 1 + lv;
          const dmg = (1.0 + 0.5 * lv) * power;
          for (let j = 0; j <= jumps; j++) {
            if (!cur || hitSet.has(cur)) break;
            hitSet.add(cur);
            this.beams.push({ x1: from.x, y1: from.y, x2: cur.x, y2: cur.y, life: 0.12 });
            cur.hp -= dmg;
            from = cur;
            cur = this.nearestEnemy(from.x, from.y, 200, hitSet);
          }
        }
      }
    }
    if (p.weapons.ORB) {
      const lv = p.weapons.ORB;
      p.orbA += dt * 2.2;
      const n = lv + 1;
      const dps = (15 + 7 * lv) * power;
      for (let i = 0; i < n; i++) {
        const a = p.orbA + (Math.PI * 2 * i) / n;
        const ox = p.x + Math.cos(a) * 58;
        const oy = p.y + Math.sin(a) * 58;
        for (const e of this.enemies) {
          if (Math.hypot(e.x - ox, e.y - oy) < 9 + e.r) e.hp -= dps * dt;
        }
      }
    }
    if (p.weapons.AURA) {
      const lv = p.weapons.AURA;
      const r = 92 + 19 * lv;
      const dps = (5 + 2.5 * lv) * power;
      for (const e of this.enemies) {
        if (Math.hypot(e.x - p.x, e.y - p.y) < r + e.r) {
          const big = e.kind === "tank" || e.kind === "elite" || e.kind === "boss";
          e.hp -= dps * dt * (big ? 0.55 : 1.0);
          const sl = big ? 0.8 : 0.55;
          e.slowT = Math.max(e.slowT || 0, 0.15);
          e.slowF = sl;
        }
      }
    }
    if (p.weapons.NOVA) {
      const lv = p.weapons.NOVA;
      p.novaT -= dt;
      if (p.novaT <= 0) {
        p.novaT = Math.max(1.1, 2.8 - 0.25 * lv);
        const r = 165 + 22 * lv;
        const dmg = (6 + 3 * lv) * power;
        for (const e of this.enemies) {
          const d = Math.hypot(e.x - p.x, e.y - p.y);
          if (d < r + e.r) {
            e.hp -= dmg;
            const nx = (e.x - p.x) / (d || 1), ny = (e.y - p.y) / (d || 1);
            e.x += nx * 38; e.y += ny * 38;
          }
        }
        this.marks.push({ x: p.x, y: p.y, r, life: 0.35, col: C.nova });
      }
    }
  }

  fire(p, e, dmg, power, spd, col) {
    if (this.bullets.length >= MAX_BULLETS) return;
    const dx = e.x - p.x, dy = e.y - p.y;
    const d = Math.hypot(dx, dy) || 1;
    this.bullets.push({ x: p.x, y: p.y, vx: dx / d * spd, vy: dy / d * spd,
      dmg: dmg * power, r: 4, life: 1.2, col: col === "bolt" ? "#9fd8ff" : "#8fd6a0",
      pierce: 0 });
  }

  nearestEnemy(x, y, maxD, exclude) {
    let best = null, bd = maxD;
    for (const e of this.enemies) {
      if (exclude && exclude.has(e)) continue;
      const d = Math.hypot(e.x - x, e.y - y);
      if (d < bd) { bd = d; best = e; }
    }
    return best;
  }

  nearestEnemies(x, y, maxD, n) {
    const arr = this.enemies
      .map(e => ({ e, d: Math.hypot(e.x - x, e.y - y) }))
      .filter(o => o.d < maxD)
      .sort((a, b) => a.d - b.d)
      .slice(0, n)
      .map(o => o.e);
    return arr;
  }

  // ---------------------------------------------- 敌人
  updateEnemies(dt) {
    const ps = this.dual ? [this.p1, this.p2] : [this.p1];
    for (const e of this.enemies) {
      let tgt = ps[0], bd = Infinity;
      for (const p of ps) {
        const d = Math.hypot(p.x - e.x, p.y - e.y);
        if (d < bd) { bd = d; tgt = p; }
      }
      let slow = 1;
      if (e.slowT > 0) { e.slowT -= dt; slow = e.slowF || 1; }
      if (this.lull > 0) slow = Math.min(slow, 0.45);
      const dx = tgt.x - e.x, dy = tgt.y - e.y;
      const d = Math.hypot(dx, dy) || 1;
      e.x += dx / d * e.spd * slow * dt;
      e.y += dy / d * e.spd * slow * dt;
      for (const p of ps) {
        if (p.inv > 0) continue;
        if (Math.hypot(p.x - e.x, p.y - e.y) < e.r + PLAYER_R) {
          p.hp -= e.dmg;
          p.inv = INVULN;
          this.burst(p.x, p.y, "#505af0", 10, 200);
        }
      }
    }
    // 分离
    for (let i = 0; i < this.enemies.length; i++) {
      for (let j = i + 1; j < this.enemies.length; j++) {
        const a = this.enemies[i], b = this.enemies[j];
        const dx = b.x - a.x, dy = b.y - a.y;
        const d = Math.hypot(dx, dy) || 1;
        const min = a.r + b.r;
        if (d < min) {
          const push = (min - d) / 2;
          a.x -= dx / d * push; a.y -= dy / d * push;
          b.x += dx / d * push; b.y += dy / d * push;
        }
      }
    }
    // 死亡结算
    const alive = [];
    for (const e of this.enemies) {
      if (e.hp > 0) { alive.push(e); continue; }
      this.stats.kills++;
      this.burst(e.x, e.y, e.col, 8, 160);
      if (e.kind === "splitter") {
        for (let i = 0; i < 2; i++) {
          alive.push({ kind: "grunt", x: e.x + rnd(-14, 14), y: e.y + rnd(-14, 14),
            hp: 0.7, maxHp: 0.7, spd: 70, r: 7, dmg: 4, xp: 1, col: C.split });
        }
      }
      const g = Math.max(1, Math.round(e.xp / 2));
      for (let i = 0; i < g; i++) {
        if (this.gems.length < MAX_GEMS) {
          this.gems.push({ x: e.x + rnd(-10, 10), y: e.y + rnd(-10, 10),
                           v: e.xp / g, r: 4 });
        }
      }
    }
    this.enemies = alive;

    // 子弹推进
    const keepB = [];
    for (const b of this.bullets) {
      b.x += b.vx * dt; b.y += b.vy * dt; b.life -= dt;
      if (b.life <= 0 || b.x < -40 || b.x > PW + 40 || b.y < PLAY_T - 40 || b.y > PLAY_B + 40) continue;
      let hit = false;
      for (const e of this.enemies) {
        if (Math.hypot(e.x - b.x, e.y - b.y) < e.r + b.r) {
          e.hp -= b.dmg; hit = true; break;
        }
      }
      if (!hit) keepB.push(b);
    }
    this.bullets = keepB;
    this.updateErrWindow();
  }

  // ---------------------------------------------- 经验
  updateGems(dt) {
    const ps = this.dual ? [this.p1, this.p2] : [this.p1];
    const keep = [];
    for (const g of this.gems) {
      let owner = ps[0], bd = Infinity;
      for (const q of ps) {
        const d = Math.hypot(q.x - g.x, q.y - g.y);
        if (d < bd) { bd = d; owner = q; }
      }
      const pullR = 92 * (1 + 0.30 * (owner.passives.MAGNET || 0));
      if (bd < pullR && bd > 1) {
        const s = 260 * dt / bd;
        g.x += (owner.x - g.x) * s;
        g.y += (owner.y - g.y) * s;
      }
      if (bd < 22) { owner.xp += g.v; continue; }
      keep.push(g);
    }
    this.gems = keep;

    for (const p of ps) {
      if (p.xp >= p.need) {
        p.xp -= p.need;
        p.level++;
        p.need = Math.round(6 + p.level * 4 + p.level * p.level * 0.6);
        this.openLevelup(p);
        return;   // 一次只弹一个
      }
    }
  }

  updateFx(dt) {
    for (const m of this.marks) { m.life -= dt; }
    this.marks = this.marks.filter(m => m.life > 0);
    for (const b of this.beams) { b.life -= dt; }
    this.beams = this.beams.filter(b => b.life > 0);
    for (const f of this.floats) { f.y -= 30 * dt; f.life -= dt; }
    this.floats = this.floats.filter(f => f.life > 0);

    if (!this.particles) this.particles = [];
    for (const p of this.particles) {
      p.x += p.vx * dt; p.y += p.vy * dt;
      p.vx *= 0.92; p.vy *= 0.92; p.life -= dt;
    }
    this.particles = this.particles.filter(p => p.life > 0);
  }

  burst(x, y, col, n, spd) {
    if (!this.particles) this.particles = [];
    for (let i = 0; i < n; i++) {
      const a = Math.random() * Math.PI * 2;
      const s = spd * rnd(0.35, 1);
      this.particles.push({ x, y, vx: Math.cos(a) * s, vy: Math.sin(a) * s,
        life: rnd(0.25, 0.6), col, r: rnd(1.2, 3) });
    }
    if (this.particles.length > 320) this.particles.splice(0, this.particles.length - 320);
  }

  // ---------------------------------------------- 升级选卡
  // 升级选卡：进场保护 -> 迟滞判定 -> 保持足够久才生效
  // 迟滞阈值：进 0.32 / 出 0.18（避免手在阈值边缘抖动时反复清零）
  LEVELUP_GRACE = 0.6;
  LEVELUP_HOLD = 0.9;
  LEVELUP_TIMEOUT = 8.0;

  updateLevelup(dt, hand) {
    const lu = this.levelup;
    if (!lu) { this.mode = "play"; return; }
    lu.since += dt;

    // 进场保护：先让人看清楚两张卡，期间不接收任何选择
    if (lu.since < this.LEVELUP_GRACE) { lu.side = 0; lu.hold = 0; return; }

    let dev = null;
    if (hand && this.reach.lo !== null) {
      const span = Math.max(0.08, this.reach.hi - this.reach.lo);
      const rel = clamp((hand.palm.x - this.reach.lo) / span, 0, 1);
      dev = rel - 0.5;
    }

    let side = lu.side;
    if (dev === null) {
      side = 0;
    } else if (side === 0) {
      if (dev < -0.32) side = -1;
      else if (dev > 0.32) side = 1;
    } else {
      if (Math.abs(dev) < 0.18) side = 0;
      else side = dev > 0 ? 1 : -1;
    }

    if (side !== lu.side) { lu.side = side; lu.hold = 0; }
    else if (side !== 0) lu.hold += dt;

    if (side !== 0 && lu.hold >= this.LEVELUP_HOLD) {
      const c = side < 0 ? lu.choices[0] : lu.choices[1];
      this.applyChoice(c, lu.owner || this.activePlayer());
      return;
    }
    // 兜底：一直不选就自动拿第一张，但留足 8 秒
    if (lu.since > this.LEVELUP_TIMEOUT) {
      this.applyChoice(lu.choices[0], lu.owner || this.activePlayer());
    }
  }
}
