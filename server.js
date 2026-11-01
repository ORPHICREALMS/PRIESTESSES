// Orphic Realm: the shared world. One copy of the game, everyone plays it here.
// The server keeps the clock, passes everyone's position around, and tells each player about the people near them.
const http = require('http'), fs = require('fs'), path = require('path'), zlib = require('zlib');
const { Server } = require('socket.io');
const PORT = process.env.PORT || 10000, DAY_LEN = 480, TICK_MS = 100, NEAR = 140, MAX_PLAYERS = 300, BOUND = 200000;
// serves index.html if it is there; otherwise the newest orphic-realm-vNN.html in this folder
const gameFile = fs.existsSync(path.join(__dirname, 'index.html')) ? 'index.html' : fs.readdirSync(__dirname).filter(f => /^orphic-realm-v[\d.]+\.html$/.test(f)).sort((a, b) => a.replace(/\D+/g, ' ').trim().split(' ').map(Number).reduce((r, v, i, arr) => r || (v - (b.replace(/\D+/g, ' ').trim().split(' ').map(Number)[i] || 0)), 0)).pop();
if (!gameFile) throw new Error('Put the game next to server.js as index.html (or orphic-realm-vNN.html).');
console.log('Serving ' + gameFile);
const gz = zlib.gzipSync(fs.readFileSync(path.join(__dirname, gameFile)), { level: 9 });
const server = http.createServer((req, res) => {
  const u = req.url.split('?')[0];
  if (u === '/health') { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, online: players.size })); }
  if (u === '/' || u === '/play' || u === '/index.html') {
    const ok = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache', ...(ok ? { 'Content-Encoding': 'gzip' } : {}) });
    return res.end(ok ? gz : zlib.gunzipSync(gz));
  }
  res.writeHead(404); res.end('Not found');
});
const io = new Server(server, { maxHttpBufferSize: 1e5, pingInterval: 20000, pingTimeout: 20000 });
const ns = io.of('/world'), players = new Map();
const byId = id => { for (const p of players.values()) if (p.id === id) return p; return null; };
const epoch = Date.now() - 0.3 * DAY_LEN * 1000, clock = () => (((Date.now() - epoch) / 1000) / DAY_LEN) % 1;
const clean = (v, n) => String(v == null ? '' : v).replace(/[\u0000-\u001f<>]/g, '').trim().slice(0, n);
const num = (v, d = 0) => (typeof v === 'number' && isFinite(v)) ? v : d;
// ===== the world's monsters and villagers, run here so everyone sees the same thing =====
const TAU = Math.PI * 2, clamp = (v, a, b) => Math.max(a, Math.min(b, v)), rnd = (a, b) => a + Math.random() * (b - a);
const smooth = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
const lerpAngle = (a, b, t) => { let d = (b - a) % TAU; if (d > Math.PI) d -= TAU; if (d < -Math.PI) d += TAU; return a + d * t; };
let SIM = null;
try {
  const html = fs.readFileSync(path.join(__dirname, gameFile), 'utf8'), m = html.match(/<script type="application\/json" id="orsim">([\s\S]*?)<\/script>/);
  if (m) {
    const j = JSON.parse(m[1]), bits = Buffer.from(j.grid.b64, 'base64');
    SIM = { edef: j.edef, groups: j.groups, g: j.grid, bits, mons: [], npcs: [], proj: [], nid: 0 };
  }
} catch (e) { console.log('sim load failed', e.message); }
console.log(SIM ? 'World simulation on: ' + SIM.groups.length + ' monster groups' : 'No world data in the game file: monsters stay local');
// the two caves under the small island: the monsters in them are run here too, so everyone in a cave sees (and fights) the same ones
const ROOMS = {
  C1: { cx: 31400, rad: 16.1, groups: [['ghoul', -6, 4, 1, 3], ['phantom', 7, 2, 1, 3], ['werebeast', -5, -4, 1, 2], ['mossback', 0, -10.5, 1, 1]] },
  C2: { cx: 31900, rad: 18.1, groups: [['ghoul', -7, 5, 3, 4], ['phantom', 8, 3, 3, 4], ['werebeast', -6, -4, 3, 3], ['troll', 8, -5, 2, 2], ['demon', 0, -8, 2, 3], ['mossback', 0, -12.5, 1, 1]] }
};
const roomAt = x => { if (x < 20000) return null; for (const k in ROOMS) if (Math.abs(x - ROOMS[k].cx) < 30) return k; return null; };
const rz = p => String(p.zone || '').split('@')[0];   // the game sends 'C1@295,302' (room + the door it came in by)
const inSim = z => z === '' || !!ROOMS[z];
const walkW = (x, z) => { const g = SIM.g, i = Math.round((x - g.x0) / g.res), j = Math.round((z - g.x0) / g.res); if (i < 0 || j < 0 || i >= g.n || j >= g.n) return false; const k = j * g.n + i; return (SIM.bits[k >> 3] >> (k & 7)) & 1; };
const walkable = (x, z) => { if (x > 20000) { const k = roomAt(x); return !!k && Math.hypot(x - ROOMS[k].cx, z) < ROOMS[k].rad; } return walkW(x, z); };
const moveEnt = (e, dx, dz) => {
  const rm = e.x > 20000, nx = rm ? e.x + dx : clamp(e.x + dx, -122, 122), nz = rm ? e.z + dz : clamp(e.z + dz, -122, 122);
  if (e.ghost || e.fly) { e.x = nx; e.z = nz; return; }
  if (walkable(nx, nz)) { e.x = nx; e.z = nz; } else if (walkable(nx, e.z)) e.x = nx; else if (walkable(e.x, nz)) e.z = nz;
};
function spotNear(cx, cz, spread) { for (let i = 0; i < 30; i++) { const a = Math.random() * TAU, d = Math.sqrt(Math.random()) * spread, x = cx + Math.cos(a) * d, z = cz + Math.sin(a) * d; if (walkable(x, z)) return { x, z }; } return { x: cx, z: cz }; }
function nightNow() { const s = Math.sin((clock() - .25) * TAU); return 1 - smooth(-.12, .12, s); }
function spawnMon(kind, x, z, grp) {
  const d = SIM.edef[kind], e = { nid: 'm' + (++SIM.nid), kind, def: d, x, z, yaw: Math.random() * TAU, hp: d.hp, max: d.hp, r: d.r, dead: false, deadT: 0, home: { x, z }, state: 'idle', wanderT: rnd(0, 3), wander: null, target: null, aggroBoost: 0, atkT: rnd(.2, 1.5), abT: rnd(1, 4), atk: null, moving: false, spdMul: 1, group: grp, fly: !!d.fly, ghost: !!d.ghost, orbit: 0, lunge: null, st: {}, kv: { x: 0, z: 0 } };
  SIM.mons.push(e); return e;
}
const STORY = { marrow: { gone: false, back: 0, x: 47.5, z: -5.5 }, wren: { gone: false, back: 0, x: 4.5, z: 46 } };
const storyState = () => ({ marrow: STORY.marrow.gone, wren: STORY.wren.gone });
function storyAct(me, d) {
  const act = clean(d.act, 10), s = STORY[d.id]; if (!s) return;
  if (d.id === 'wren' && act === 'steal') {   // a companion Wren stole this player's gold and runs for the bandit camp
    const m = spawnMon('wren', clamp(num(d.x, me.x), -120, 120), clamp(num(d.z, me.z), -120, 120), null); m.state = 'flee'; m.story = true; m.loot = clamp(Math.round(num(d.amt)), 0, 100000); m.victim = me.sid; return;
  }
  if (s.gone) return;
  if (d.id === 'marrow' && ['take', 'refuse', 'name'].includes(act)) {
    s.gone = true; s.back = Date.now() + 600000;
    if (act !== 'refuse') { const h = spawnMon('hag', s.x, s.z, null); h.story = true; h.aggroBoost = 30; h.target = me; if (act === 'take') for (let i = 0; i < 2; i++) { const sp = spotNear(s.x, s.z, 6), g = spawnMon('ghoul', sp.x, sp.z, null); g.story = true; g.home = { x: s.x, z: s.z }; g.aggroBoost = 30; g.target = me; } }
  } else if (d.id === 'wren' && (act === 'recruit' || act === 'expose')) {
    s.gone = true; s.back = Date.now() + 600000;
    if (act === 'expose') { const m = spawnMon('wren', s.x, s.z, null); m.state = 'flee'; m.story = true; m.loot = 0; }
  } else return;
  ns.emit('story', { id: d.id, gone: true, by: me.id });
}
function initSim() {
  if (!SIM) return;
  for (const g of SIM.groups) { g.members = []; g.timer = -1; g.m.forEach(p => g.members.push(spawnMon(g.kind, p[0], p[1], g))); }
  for (const k in ROOMS) for (const r of ROOMS[k].groups) {
    if (!SIM.edef[r[0]]) continue;
    const g = { kind: r[0], cx: ROOMS[k].cx + r[1], cz: r[2], n: r[3], spread: r[4], members: [], timer: -1, zone: k };
    for (let i = 0; i < g.n; i++) { const sp = spotNear(g.cx, g.cz, g.spread), e = spawnMon(g.kind, sp.x, sp.z, g); e.zone = k; g.members.push(e); }
    SIM.groups.push(g);
  }
}
const live = () => { const out = []; for (const p of players.values()) if (inSim(rz(p)) && !p.dead) out.push(p); return out; };
const send = (p, ev, d) => { const s = ns.sockets.get(p.sid); if (s) s.emit(ev, d); };
const nearPlayers = (x, z, r) => { const out = [], zk = roomAt(x) || ''; for (const p of players.values()) if (rz(p) === zk && Math.hypot(p.x - x, p.z - z) <= r) out.push(p); return out; };
const hitPlayer = (p, amt, type, from, f, spark) => {
  let kx = 0, kz = 0; if (from && f) { const d = Math.hypot(p.x - from.x, p.z - from.z) || 1; kx = (p.x - from.x) / d; kz = (p.z - from.z) / d; }
  send(p, 'hurtp', { amt: Math.round(amt), type, kx, kz, kf: f || 0, spark: spark || 0 });
};
const los = (x0, z0, x1, z1) => { const d = Math.hypot(x1 - x0, z1 - z0), n = Math.ceil(d / .5); let b = 0; for (let i = 1; i < n; i++) { const t = i / n; if (!walkable(x0 + (x1 - x0) * t, z0 + (z1 - z0) * t)) { if (++b >= 2) return false; } else b = 0; } return true; };   // walls, rocks and trees block attacks
const AGGRO_K = .75;   // monsters notice you from a bit closer than before
const crowdOf = e => Math.max(1, nearPlayers(e.x, e.z, 40).filter(p => !p.dead).length);
const bigOne = e => !!(e.def.boss || (e.def.tags || []).includes('troll'));
const dmgRoll = e => e.def.dmg * (.9 + Math.random() * .2) * (e.def.nightBoost ? 1 + .15 * nightNow() : 1) * (bigOne(e) ? 1 + Math.min(.25, .06 * (crowdOf(e) - 1)) : 1);
const fx = (x, z, d) => { for (const p of nearPlayers(x, z, 150)) send(p, 'fx', d); };
function beginAtk(e, dur, hit, fn) { e.atk = { t: 0, dur, hit, did: false, fn }; }
function toward(e, tx, tz, speed, dt, stop = 0) {
  const dx = tx - e.x, dz = tz - e.z, d = Math.hypot(dx, dz); if (d <= stop || d < .001) return d;
  const step = Math.min(speed * e.spdMul * dt, d - stop); moveEnt(e, dx / d * step, dz / d * step); e.yaw = lerpAngle(e.yaw, Math.atan2(dx, dz), Math.min(1, dt * 9)); e.moving = true; return d;
}
const face = (e, tx, tz, dt) => { e.yaw = lerpAngle(e.yaw, Math.atan2(tx - e.x, tz - e.z), Math.min(1, dt * 12)); };
function think(e, t, d, dt) {
  const def = e.def, dx = t.x - e.x, dz = t.z - e.z, R = .45, kind = e.kind;
  const melee = (k, kb, wind, hitAt, extra = .8) => { e.atkT = def.cd * rnd(.9, 1.2); beginAtk(e, wind, hitAt, () => { if (!t.dead && Math.hypot(t.x - e.x, t.z - e.z) <= def.range + R + extra && los(e.x, e.z, t.x, t.z)) hitPlayer(t, dmgRoll(e) * k, 'phys', e, kb); }); };
  if (kind === 'ghoul' || kind === 'bandit' || kind === 'wren') {
    if (d > def.range * .8) toward(e, t.x, t.z, def.spd, dt, def.range * .6); else face(e, t.x, t.z, dt);
    if (e.atkT <= 0 && d <= def.range + R) melee(1, 1.5, .55, .3);
  } else if (kind === 'phantom' || kind === 'hag') {
    const lo = kind === 'hag' ? 5 : 4, hi = kind === 'hag' ? 10 : 9;
    if (d > hi) toward(e, t.x, t.z, def.spd, dt, hi - 1); else if (d < lo) toward(e, e.x - dx / d * 4, e.z - dz / d * 4, def.spd, dt); else { face(e, t.x, t.z, dt); e.orbit = e.orbit || 1; moveEnt(e, -dz / d * e.orbit * 1.2 * dt, dx / d * e.orbit * 1.2 * dt); e.moving = true; }
    if (e.atkT <= 0 && d <= def.range) { e.atkT = def.cd * rnd(.9, 1.2); beginAtk(e, .9, .65, () => { if (t.dead || !los(e.x, e.z, t.x, t.z)) return; fx(e.x, e.z, { k: 'zap', x0: e.x, z0: e.z, x1: t.x, z1: t.z }); hitPlayer(t, dmgRoll(e), 'magic', null, 0, 9); if (kind === 'hag') for (const o of nearPlayers(t.x, t.z, 3)) if (o !== t) hitPlayer(o, dmgRoll(e) * .5, 'magic'); }); }
  } else if (kind === 'demon') {
    if (d > 15) toward(e, t.x, t.z, def.spd, dt, 13); else if (d < 7) toward(e, e.x - dx / d * 4, e.z - dz / d * 4, def.spd, dt); else { face(e, t.x, t.z, dt); e.orbit = e.orbit || (Math.random() < .5 ? -1 : 1); moveEnt(e, -dz / d * e.orbit * 2.2 * dt, dx / d * e.orbit * 2.2 * dt); e.moving = true; }
    if (e.atkT <= 0 && d <= def.range) { e.atkT = def.cd * rnd(.9, 1.3); beginAtk(e, .7, .5, () => { if (t.dead) return; const l = Math.hypot(t.x - e.x, t.z - e.z) || 1; SIM.proj.push({ x: e.x, z: e.z, vx: (t.x - e.x) / l * 17, vz: (t.z - e.z) / l * 17, life: 2.4, r: .5, aoe: 1.8, dmg: dmgRoll(e), kf: 3, col: 0xff7a2a }); fx(e.x, e.z, { k: 'proj', x0: e.x, z0: e.z, x1: e.x + (t.x - e.x) / l * 17 * 2.4, z1: e.z + (t.z - e.z) / l * 17 * 2.4, sp: 17, life: 2.4, col: 0xff7a2a, sz: 1.4 }); }); }
  } else if (kind === 'werebeast') {
    if (e.lunge) { e.lunge.t -= dt; moveEnt(e, e.lunge.x * dt, e.lunge.z * dt); e.moving = true; if (e.lunge.t <= 0) { e.lunge = null; if (d < 3.4 && los(e.x, e.z, t.x, t.z)) hitPlayer(t, dmgRoll(e) * 1.4, 'phys', e, 5); } return; }
    if (e.abT <= 0 && d > 4 && d < 10) { e.abT = 5; e.lunge = { t: .38, x: dx / d * 17, z: dz / d * 17 }; e.lungeAnim = true; return; }
    if (d > def.range * .8) toward(e, t.x, t.z, def.spd, dt, def.range * .6); else face(e, t.x, t.z, dt);
    if (e.atkT <= 0 && d <= def.range + R) { e.atkT = def.cd * rnd(.9, 1.15); beginAtk(e, .5, .28, () => { if (!t.dead && Math.hypot(t.x - e.x, t.z - e.z) <= def.range + R + .9 && los(e.x, e.z, t.x, t.z)) hitPlayer(t, dmgRoll(e), 'phys', e, 3); }); }
  } else if (kind === 'troll' || kind === 'mossback') {
    const boss = kind === 'mossback', enr = boss && e.hp < e.max * .4 ? 1.25 : 1; e.spdMul *= enr;
    if (boss && e.abT <= 0 && d > 9 && d < 24) {
      e.abT = 6.5; const tx = t.x, tz = t.z; fx(tx, tz, { k: 'ring', x: tx, z: tz, r: 3.6, t: 1.2 });
      beginAtk(e, 1.1, .8, () => { const fly = clamp(Math.hypot(tx - e.x, tz - e.z) / 15, .5, 1.6); fx(e.x, e.z, { k: 'proj', x0: e.x, z0: e.z, x1: tx, z1: tz, sp: Math.hypot(tx - e.x, tz - e.z) / fly, life: fly, col: 0x8a8a7a, sz: 2.4, arc: 1 }); SIM.proj.push({ x: tx, z: tz, land: fly, aoe: 3.6, dmg: def.dmg * .8, kf: 6, col: 0x8a8a7a }); });
      return;
    }
    if (d > def.range * .85) toward(e, t.x, t.z, def.spd, dt, def.range * .7); else face(e, t.x, t.z, dt);
    if (e.atkT <= 0 && d <= def.range + R + 1) {
      e.atkT = def.cd * rnd(.9, 1.1) / (enr > 1 ? 1.3 : 1); const RR = boss ? 7.5 : 5.2, cx = e.x, cz = e.z;
      fx(cx, cz, { k: 'ring', x: cx, z: cz, r: RR, t: 1.1 });
      beginAtk(e, 1.15, .95, () => { fx(cx, cz, { k: 'boom', x: cx, z: cz }); for (const o of nearPlayers(cx, cz, RR + R)) if (los(cx, cz, o.x, o.z)) hitPlayer(o, dmgRoll(e), 'phys', { x: cx, z: cz }, 9); });
    }
  }
}
function stepMon(e, dt, pls) {
  if (e.dead) { e.deadT += dt; return; }
  e.atkT -= dt; e.abT -= dt; e.aggroBoost -= dt; e.moving = false;
  for (const k in e.st) { const t = e.st[k]; t.t -= dt; if (k === 'burn') { t.acc = (t.acc || 0) + t.v * dt; if (t.acc >= 3) { const a = Math.floor(t.acc); t.acc -= a; damageMon(e, a, 'fire', t.sid, true); if (e.dead) return; } } if (t.t <= 0) delete e.st[k]; }
  if (Math.abs(e.kv.x) + Math.abs(e.kv.z) > .05) { moveEnt(e, e.kv.x * dt, e.kv.z * dt); const k = Math.exp(-7 * dt); e.kv.x *= k; e.kv.z *= k; }
  e.spdMul = (e.st.slow ? 1 - e.st.slow.v : 1) * (e.def.nightBoost ? 1 + .15 * nightNow() : 1) * (e.st.root ? 0 : 1) * (e.st.haste ? 1.2 : 1);
  if (e.st.stun) return;
  if (e.state === 'flee') { e.fleeFear = (e.fleeFear || 0) - dt; const cx = 67, cz = -74, d = Math.hypot(cx - e.x, cz - e.z); if (d > 7) toward(e, cx, cz, e.def.spd * (e.fleeFear > 0 ? 1.15 : 1), dt); else { e.state = 'idle'; e.home = { x: cx, z: cz }; } return; }
  if (e.atk) { e.atk.t += dt; if (!e.atk.did && e.atk.t >= e.atk.hit) { e.atk.did = true; e.atk.fn(); } if (e.atk.t >= e.atk.dur) e.atk = null; return; }
  if (e.st.taunt) { const tp = players.get(e.st.taunt.sid); if (tp && !tp.dead && rz(tp) === (e.zone || '')) e.target = tp; }
  if (e.st.blind) e.target = null;
  if (e.target && (e.target.dead || rz(e.target) !== (e.zone || '') || !players.has(e.target.sid))) e.target = null;
  if (!e.target && !e.st.blind) { let range = e.def.aggro * AGGRO_K * (e.aggroBoost > 0 ? 1.6 : 1); if (e.def.nightAggro) range *= 1 + .25 * nightNow(); let bd = range; for (const p of pls) { if (p.stealth) continue; const dd = Math.hypot(p.x - e.x, p.z - e.z); if (dd < bd && (e.aggroBoost > 0 || los(e.x, e.z, p.x, p.z))) { bd = dd; e.target = p; } } if (e.target) e.atkT = Math.max(e.atkT, 1.2); }
  if (e.target) {
    const t = e.target, dh = Math.hypot(e.x - e.home.x, e.z - e.home.z), d = Math.hypot(t.x - e.x, t.z - e.z) || .001;
    if (dh > e.def.leash || d > e.def.aggro * 2.4) { e.target = null; e.state = 'return'; } else { e.state = 'fight'; think(e, t, d, dt); }
  } else {
    const dh = Math.hypot(e.x - e.home.x, e.z - e.home.z);
    if (e.state === 'return' || dh > 22) { e.state = 'return'; toward(e, e.home.x, e.home.z, e.def.spd * 1.1, dt, 2); e.hp = Math.min(e.max, e.hp + e.max * .1 * dt); if (dh < 3) e.state = 'idle'; }
    else { e.wanderT -= dt; if (e.wanderT <= 0) { e.wanderT = rnd(2.5, 6); e.wander = Math.random() < .6 ? spotNear(e.home.x, e.home.z, 7) : null; } if (e.wander) { const d = toward(e, e.wander.x, e.wander.z, e.def.spd * .35, dt, .8); if (d < 1) e.wander = null; } }
    e.hp = Math.min(e.max, e.hp + e.max * .01 * dt);
  }
  for (const o of SIM.mons) { if (o === e || o.dead) continue; const dx = e.x - o.x, dz = e.z - o.z, m = (e.r + o.r) * .85, d2 = dx * dx + dz * dz; if (d2 < m * m && d2 > 1e-6) { const d = Math.sqrt(d2), push = (m - d) * .5; moveEnt(e, dx / d * push, dz / d * push); } }
}
function stepProj(dt) {
  for (let i = SIM.proj.length - 1; i >= 0; i--) {
    const p = SIM.proj[i]; let boom = false;
    if (p.land != null) { p.land -= dt; boom = p.land <= 0; }
    else { p.x += p.vx * dt; p.z += p.vz * dt; p.life -= dt; if (!walkable(p.x, p.z)) p.life = 0; for (const q of nearPlayers(p.x, p.z, 1.4)) if (!q.dead) boom = true; if (p.life <= 0) boom = true; }
    if (boom) { for (const q of nearPlayers(p.x, p.z, p.aoe + .45)) hitPlayer(q, p.dmg, p.land != null ? 'phys' : 'fire', { x: p.x, z: p.z }, p.kf); fx(p.x, p.z, { k: 'boom', x: p.x, z: p.z, col: p.col }); SIM.proj.splice(i, 1); }
  }
}
function killMon(e, killerSid) {
  e.dead = true; e.deadT = 0; e.target = null; e.atk = null; e.hp = 0;
  for (const p of nearPlayers(e.x, e.z, 150)) if ((e.hitters && e.hitters.has(p.sid)) || Math.hypot(p.x - e.x, p.z - e.z) < 25) send(p, 'ekill', { kind: e.kind, x: +e.x.toFixed(1), z: +e.z.toFixed(1) });
  if (e.kind === 'wren' && e.victim) { const v = players.get(e.victim); if (v) send(v, 'storyloot', { amt: e.loot || 0 }); }
  const g = e.group; if (g && g.members.every(m => m.dead)) g.timer = 110;
}
function damageMon(e, amt, type, sid, dot) {
  if (e.dead) return; let a = Math.max(0, Math.min(2000, amt)); const tags = e.def.tags || [];
  if (type === 'holy' && (tags.includes('undead') || tags.includes('demon'))) a *= 1.6; if (type === 'phys' && e.def.physResist) a *= e.def.physResist;
  if (e.st.brittle) a *= 1.3; if (e.st.mark) a *= 1.35;
  if (e.state === 'flee') e.fleeFear = 2;
  if (bigOne(e)) a /= 1 + Math.min(.6, .15 * (crowdOf(e) - 1));   // the more people at a big fight, the tougher it gets
  if (sid) (e.hitters || (e.hitters = new Set())).add(sid);
  e.hp -= a; const me = players.get(sid); if (!dot) { e.aggroBoost = 6; if (!e.target && me && !me.dead) e.target = me; }
  if (e.hp <= 0) killMon(e, sid);
}
function hitMon(nid, amt, type, crit, sid, kb) {
  const e = SIM.mons.find(m => m.nid === nid), me = players.get(sid); if (!e || e.dead || !me) return;
  if (Math.hypot(me.x - e.x, me.z - e.z) > 70) return;
  damageMon(e, amt, type, sid);
  if (kb && !e.def.heavy && !e.dead) { e.kv.x += clamp(num(kb[0]), -1.5, 1.5) * clamp(num(kb[2]), 0, 12); e.kv.z += clamp(num(kb[1]), -1.5, 1.5) * clamp(num(kb[2]), 0, 12); }
}
const STAT_OK = new Set(['stun', 'slow', 'root', 'taunt', 'blind', 'burn', 'brittle', 'mark']);
function statMon(nid, key, dur, v, sid) {
  const e = SIM.mons.find(m => m.nid === nid), me = players.get(sid); if (!e || e.dead || !me || !STAT_OK.has(key)) return;
  if (Math.hypot(me.x - e.x, me.z - e.z) > 70) return; dur = clamp(num(dur), 0, 15); v = clamp(num(v, 1), 0, 100);
  const cur = e.st[key]; if (cur && key !== 'burn') { cur.t = Math.max(cur.t, dur); cur.v = v; } else e.st[key] = { t: dur, v, sid };
}
const BLESS = { until: 0, t: 0, cool: 0, tell: 0 }, DANCES = new Set(['dance', 'waltz', 'courtly', 'folk', 'twirl']);
const PITS = [{ id: 'f0', x: -8, z: -18 }, { id: 'f1', x: 10, z: 18 }, { id: 'f2', x: -12, z: 20 }, { id: 'f3', x: 14, z: -22 }, { id: 'f4', x: 12, z: -10 }];
for (const p of PITS) p.until = 0;
const fireState = () => PITS.map(p => [p.id, Math.max(0, p.until - Date.now())]);
let partyT = 0, partyOn = false;
function socialTick(dt, now) {
  // the circle ritual: three or more people stand still around the fountain
  const c = []; for (const p of players.values()) if (p.zone === '' && !p.dead && Math.hypot(p.x, p.z) < 10 && p.mv < .05) c.push(p);
  if (c.length >= 3 && now > BLESS.cool) BLESS.t += dt; else BLESS.t = Math.max(0, BLESS.t - dt * 2);
  if (BLESS.t > 0 && now - BLESS.tell > 1000) { BLESS.tell = now; fx(0, 0, { k: 'gather', x: 0, z: 0, p: Math.min(1, BLESS.t / 8) }); }
  if (BLESS.t >= 8) { BLESS.t = 0; BLESS.until = now + DAY_LEN * 1000; BLESS.cool = now + 30000; ns.emit('bless', { left: DAY_LEN * 1000 }); fx(0, 0, { k: 'blessburst', x: 0, z: 0 }); }
  // plaza parties: dancers near the plaza
  partyT += dt;
  if (partyT >= 1) {
    partyT = 0; const d = [], cnt = {}; let m = 0;
    for (const p of players.values()) if (p.zone === '' && !p.dead && Math.hypot(p.x, p.z) < 35 && DANCES.has(p.e)) { d.push(p); cnt[p.e] = (cnt[p.e] || 0) + 1; m = Math.max(m, cnt[p.e]); }
    if (d.length >= 2) { partyOn = true; for (const p of nearPlayers(0, 0, 70)) send(p, 'party', { n: d.length, m }); }
    else if (partyOn) { partyOn = false; for (const p of nearPlayers(0, 0, 70)) send(p, 'party', { n: 0, m: 0 }); }
  }
  // campfires burning out
  for (const p of PITS) if (p.lit && now > p.until) { p.lit = false; ns.emit('fires', fireState()); }
}
let lastSim = Date.now();
function simTick() {
  if (!SIM) return; const now = Date.now(), dt = Math.min(.25, (now - lastSim) / 1000); lastSim = now;
  socialTick(dt, now);
  for (const k in STORY) { const t = STORY[k]; if (t.gone && now > t.back) { t.gone = false; ns.emit('story', { id: k, gone: false }); } }
  const pls = live();
  if (pls.length) {
    const bz = {}; for (const p of pls) (bz[rz(p)] || (bz[rz(p)] = [])).push(p);
    for (const e of SIM.mons) { const pl = bz[e.zone || ''] || []; const near = pl.some(p => Math.hypot(p.x - e.x, p.z - e.z) < 180); if (near || e.dead || e.state === 'fight') stepMon(e, dt, pl); }
    stepProj(dt);
    for (const g of SIM.groups) if (g.timer > 0) { g.timer -= dt; if (g.timer <= 0) { if (!pls.some(p => Math.hypot(p.x - g.cx, p.z - g.cz) < 65)) { SIM.mons = SIM.mons.filter(m => !g.members.includes(m)); g.members = []; for (let i = 0; i < g.n; i++) { const s = spotNear(g.cx, g.cz, g.spread); { const m = spawnMon(g.kind, s.x, s.z, g); if (g.zone) m.zone = g.zone; g.members.push(m); } } g.timer = -1; } else g.timer = 8; } }
    for (const n of SIM.npcs) {
      n.moving = false; if (!pls.some(p => Math.hypot(p.x - n.x, p.z - n.z) < 80)) continue;
      n.wt -= dt; if (!n.tgt && n.wt <= 0) { n.wt = rnd(2, 6); n.tgt = spotNear(n.home.x, n.home.z, 6); }
      if (n.tgt) { const d = Math.hypot(n.tgt.x - n.x, n.tgt.z - n.z); if (d < .6) n.tgt = null; else { const s = 1.3 * dt; moveEnt(n, (n.tgt.x - n.x) / d * s, (n.tgt.z - n.z) / d * s); n.yaw = lerpAngle(n.yaw, Math.atan2(n.tgt.x - n.x, n.tgt.z - n.z), Math.min(1, dt * 6)); n.moving = true; } }
    }
  }
  SIM.mons = SIM.mons.filter(m => !(m.dead && m.deadT > 8));
}
function simSnap(p) {
  const out = []; if (!inSim(rz(p))) return out;
  for (const e of SIM.mons) { if ((e.zone || '') !== rz(p)) continue; if (e.dead && e.deadT > 3) continue; if (Math.hypot(p.x - e.x, p.z - e.z) > 170) continue; out.push([e.nid, e.kind, +e.x.toFixed(2), +e.z.toFixed(2), +e.yaw.toFixed(2), Math.round(e.hp), Math.round(e.max), (e.moving || e.lunge ? 1 : 0) | (e.dead ? 2 : 0) | (e.atk || e.lunge ? 4 : 0) | (e.st.stun ? 8 : 0)]); }
  if (rz(p) === '') for (const n of SIM.npcs) if (Math.hypot(p.x - n.x, p.z - n.z) < 120) out.push(['n:' + n.id, 0, +n.x.toFixed(2), +n.z.toFixed(2), +n.yaw.toFixed(2), 0, 0, n.moving ? 1 : 0]);
  return out;
}

const CHATLOG = [];   // the last few things said in the realm, so people who arrive can see them
const EMOTES = new Set(['', 'wave', 'bow', 'cheer', 'sit', 'dance', 'waltz', 'courtly', 'folk', 'twirl', 'cry', 'laugh', 'fish']);
ns.on('connection', socket => {
  if (players.size >= MAX_PLAYERS) { socket.emit('full'); return socket.disconnect(true); }
  let me = null, n = 0, win = Date.now(), cn = 0, cwin = Date.now();
  const limited = () => { const t = Date.now(); if (t - win > 1000) { win = t; n = 0; } return ++n > 40; };
  const pub = p => ({ id: p.id, name: p.name, cls: p.cls, look: p.look, x: p.x, y: p.y, z: p.z, yaw: p.yaw, zone: p.zone, e: p.e });
  socket.on('join', (d = {}) => {
    if (me || limited()) return;
    let look = null; try { const s = JSON.stringify(d.look || null); if (s.length <= 6000) look = JSON.parse(s); } catch (_) {}
    me = { id: socket.id.slice(0, 10), sid: socket.id, name: clean(d.name, 24) || 'Wanderer', cls: clean(d.cls, 24), look, x: num(d.x), y: num(d.y), z: num(d.z), yaw: num(d.yaw), mv: 0, zone: clean(d.zone, 16), e: '' };
    players.set(socket.id, me);
    socket.emit('welcome', { id: me.id, t: clock(), dayLen: DAY_LEN, online: players.size, sim: !!SIM, story: storyState(), bless: Math.max(0, BLESS.until - Date.now()), pits: PITS.map(p => [p.id, p.x, p.z]), fires: fireState() });
    socket.broadcast.emit('pjoin', pub(me));
    for (const p of players.values()) if (p !== me) socket.emit('pjoin', pub(p));
    socket.emit('chathist', CHATLOG.slice(-20));
    for (const p of players.values()) if (p !== me && p.boat) socket.emit('boat', p.boat);
    ns.emit('online', players.size);
  });
  socket.on('chat', d => {
    if (!me || !d || limited()) return;
    const m = clean(d.m, 250); if (!m) return;
    const t = Date.now(); if (t - cwin > 6000) { cwin = t; cn = 0; }
    if (++cn > 6) return socket.emit('chatno', 'Slow down a little.');   // at most 6 messages in 6 seconds
    const msg = { id: me.id, n: me.name, m, t }; CHATLOG.push(msg); if (CHATLOG.length > 30) CHATLOG.shift();
    ns.emit('chat', msg);
  });
  socket.on('boat', (d = {}) => {   // sailing: a boat's place, or someone climbing aboard / stepping off
    if (!me || limited()) return;
    const o = { id: me.id, on: d.on === 1 ? 1 : d.on === 2 ? 2 : 0, x: num(d.x), z: num(d.z), yaw: num(d.yaw), sp: num(d.sp), rid: clean(d.rid, 16) };
    if (Math.abs(o.x) > 2000 || Math.abs(o.z) > 2000) return;
    if (o.on !== 2 && !o.rid) me.boat = o;
    socket.broadcast.emit('boat', o);
  });
  socket.on('mv', (d = {}) => {
    if (!me || limited()) return;
    const x = num(d.x, me.x), z = num(d.z, me.z); if (Math.abs(x) > BOUND || Math.abs(z) > BOUND) return;
    const oz = me.zone;
    Object.assign(me, { x, y: num(d.y, me.y), z, yaw: num(d.yaw, me.yaw), mv: Math.max(0, Math.min(1, num(d.mv))), zone: clean(d.zone, 16), dead: !!d.dead, stealth: !!d.sth, w: Math.max(0, Math.min(2, Math.round(num(d.w)))) });
    if (me.zone !== oz) socket.broadcast.emit('pzone', { id: me.id, zone: me.zone });
  });
  socket.on('emote', e => {
    if (!me || limited()) return; e = clean(e, 12); if (!EMOTES.has(e)) return; me.e = e; socket.broadcast.emit('pemote', { id: me.id, e });
    if (e === 'bow') {   // two people bow to each other: a duet dance
      const now = Date.now(); me.bowAt = now;
      for (const p of players.values()) if (p !== me && p.zone === me.zone && now - (p.bowAt || 0) < 4000 && Math.hypot(p.x - me.x, p.z - me.z) < 3.5) {
        me.bowAt = p.bowAt = 0; socket.emit('duet', { with: p.id, x: p.x, z: p.z }); const s2 = ns.sockets.get(p.sid); if (s2) s2.emit('duet', { with: me.id, x: me.x, z: me.z }); break;
      }
    }
  });
  socket.on('look', look => { if (!me || limited()) return; try { const s = JSON.stringify(look || null); if (s.length <= 6000) { me.look = JSON.parse(s); socket.broadcast.emit('plook', { id: me.id, look: me.look }); } } catch (_) {} });
  // hits on monsters go to the server, which owns every monster
  socket.on('ehit', d => { if (!me || limited() || !SIM || !d) return; hitMon(clean(d.nid, 40), num(d.amt), clean(d.type, 10) || 'phys', !!d.crit, socket.id, Array.isArray(d.kb) ? d.kb : null); });
  socket.on('fire', d => { if (!me || limited() || !d) return; const p = PITS.find(q => q.id === clean(d.id, 4)); if (!p || me.zone !== '' || Math.hypot(me.x - p.x, me.z - p.z) > 6) return; p.until = Date.now() + 300000; p.lit = true; ns.emit('fires', fireState()); });
  socket.on('gift', d => { if (!me || limited() || !d) return; const t = byId(clean(d.to, 16)); if (!t || t === me || t.zone !== me.zone || Math.hypot(t.x - me.x, t.z - me.z) > 9) return; const k = clean(d.k, 8); if (!['flower', 'potion', 'gold'].includes(k)) return; const amt = k === 'gold' ? Math.max(1, Math.min(1000, Math.round(num(d.amt, 10)))) : 1; const s2 = ns.sockets.get(t.sid); if (s2) s2.emit('gift', { from: me.name, fid: me.id, k, amt }); });
  socket.on('story', d => { if (!me || limited() || !SIM || !d) return; storyAct(me, d); });
  socket.on('estat', d => { if (!me || limited() || !SIM || !d) return; statMon(clean(d.nid, 40), clean(d.key, 10), num(d.dur), num(d.v, 1), socket.id); });
  socket.on('disconnect', () => { if (!me) return; players.delete(socket.id); ns.emit('pleave', me.id); ns.emit('online', players.size); });
});
setInterval(() => {   // each person hears where the people near them are
  if (!players.size) return; const list = [...players.values()];
  for (const a of list) {
    const out = [];
    for (const b of list) { if (a === b || a.zone !== b.zone || Math.hypot(a.x - b.x, a.z - b.z) > NEAR) continue; out.push([b.id, +b.x.toFixed(2), +b.y.toFixed(2), +b.z.toFixed(2), +b.yaw.toFixed(2), +b.mv.toFixed(2), b.w | 0]); }
    const s = ns.sockets.get(a.sid); if (s) s.volatile.emit('snap', out, SIM ? simSnap(a) : null);
  }
}, TICK_MS);
setInterval(() => ns.emit('clock', clock()), 5000);
initSim(); setInterval(simTick, 100);   // keeps everyone's day and night together
server.listen(PORT, '0.0.0.0', () => console.log('Orphic Realm world on ' + PORT));
process.on('SIGTERM', () => server.close(() => process.exit(0)));
