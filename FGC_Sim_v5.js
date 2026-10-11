
'use strict';
/* FGC Sim core: Igniting Innovation 2026. Units: cm. Field 700x700, x right, y down. No DOM. */
var FGC = (function () {
  var F = 700, BR = 5, RH = 25, RR = 29, MATCH_T = 150, SKILLS_T = 150, COUNT_T = 3, SETTLE_T = 5, NB = 500;
  var ASM = { x0: 180, y0: 0, x1: 520, y1: 60 };
  var SU = { red: { x0: 180, y0: 0, x1: 290, y1: 60 }, blue: { x0: 410, y0: 0, x1: 520, y1: 60 } };
  var EXT = { x0: 290, y0: 0, x1: 410, y1: 60 };
  var SH = {
    red: { x0: 0, y0: 620, x1: 80, y1: 700, face: 80, py0: 648, py1: 672, ex: 40, ey: 612, sgn: 1 },
    blue: { x0: 620, y0: 620, x1: 700, y1: 700, face: 620, py0: 648, py1: 672, ex: 660, ey: 612, sgn: -1 }
  };
  var STARTY = [215, 350, 485];
  var CODES = ['JPN', 'BRA', 'EGY', 'KOR', 'GER', 'FRA', 'ITA', 'ESP', 'MEX', 'CAN', 'AUS', 'IND', 'TUR', 'UKR', 'POL', 'NGA', 'KEN', 'CHL', 'ARG', 'THA', 'VIE', 'UZB', 'GHA', 'MAR', 'PER', 'SWE', 'NOR', 'NZL'];
  var TPL = [
    { drive: 'tank', rpm: 400, intake: 2, hopper: 2, transfer: 2, shooter: 2, climb: 2, lift: 0 },
    { drive: 'tank', rpm: 400, intake: 2, hopper: 2, transfer: 2, shooter: 3, climb: 1, lift: 0 },
    { drive: 'tank', rpm: 350, intake: 3, hopper: 3, transfer: 3, shooter: 2, climb: 2, lift: 0 },
    { drive: 'tank', rpm: 450, intake: 2, hopper: 1, transfer: 2, shooter: 2, climb: 3, lift: 0 },
    { drive: 'tank', rpm: 350, intake: 2, hopper: 2, transfer: 3, shooter: 2, climb: 3, lift: 1 },
    { drive: 'tank', rpm: 500, intake: 1, hopper: 1, transfer: 1, shooter: 1, climb: 0, lift: 0 },
    { drive: 'tank', rpm: 450, intake: 3, hopper: 3, transfer: 4, shooter: 3, climb: 0, lift: 0 }
  ];

  function mulberry(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; var t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function angDiff(a, b) { var d = a - b; while (d > Math.PI) d -= 2 * Math.PI; while (d < -Math.PI) d += 2 * Math.PI; return d; }

  var CAPS = [6, 12, 24, 40, 60], RATES = [1.25, 2, 3, 4.5, 6];
  function defaultCfg() { return { drive: 'tank', rpm: 400, intake: 2, hopper: 2, transfer: 2, shooter: 2, climb: 2, lift: 0 }; }
  function normCfg(c) {
    var d = defaultCfg(), o = { drive: 'tank' }; c = c || {};
    var rpm = isFinite(c.rpm) && c.rpm !== null ? +c.rpm : (isFinite(c.speed) && c.speed ? 300 + (c.speed - 1) * 50 : d.rpm);
    o.rpm = clamp(Math.round(rpm / 25) * 25, 300, 500);
    [['intake', 3], ['hopper', 5], ['transfer', 5], ['shooter', 5]].forEach(function (k) {
      var v = Math.round(+c[k[0]]); if (!(v >= 1)) v = d[k[0]]; o[k[0]] = clamp(v, 1, k[1]);
    });
    var cl = Math.round(+c.climb); o.climb = isFinite(cl) ? clamp(cl, 0, 3) : d.climb;
    var lf = Math.round(+c.lift); o.lift = isFinite(lf) ? clamp(lf, 0, 1) : d.lift;
    return o;
  }
  function derive(c) {
    return { vmax: c.rpm * 0.25, iw: [26, 38, 50][c.intake - 1], cap: CAPS[c.hopper - 1], rate: RATES[c.transfer - 1], shoot: c.shooter, cl: c.climb, lift: c.lift, vclimb: 16 + 6 * c.climb, mass: 1 + (500 - c.rpm) / 200, mec: false };
  }

  function mkBrace(team) {
    var a = team === 'red' ? { x: 122, y: 672 } : { x: 578, y: 672 }, b = team === 'red' ? { x: 303, y: 78 } : { x: 397, y: 78 };
    var dx = b.x - a.x, dy = b.y - a.y, L = Math.hypot(dx, dy), ux = dx / L, uy = dy / L, nx = -uy, ny = ux;
    if (nx * (350 - (a.x + b.x) / 2) + ny * (350 - (a.y + b.y) / 2) < 0) { nx = -nx; ny = -ny; }
    return { a: a, b: b, L: L, ux: ux, uy: uy, nx: nx, ny: ny };
  }
  function pipePt(b, t) { return { x: b.a.x + b.ux * b.L * t, y: b.a.y + b.uy * b.L * t }; }
  function zoneOf(t) { return t <= 1 / 3 + 1e-9 ? 1 : t <= 2 / 3 + 1e-9 ? 2 : 3; }
  function sMax(cl) { return cl >= 3 ? 0.955 : cl / 3; }

  function mkRobot(id, team, slot, cfg, human, code) {
    return {
      id: id, team: team, slot: slot, human: human, code: code, cfg: cfg, d: derive(cfg),
      x: team === 'red' ? RR + 1 : F - RR - 1, y: STARTY[slot], th: team === 'red' ? 0 : Math.PI, vx: 0, vy: 0, om: 0,
      goals: 0, held: [], intakeOn: true, ejCd: 0, inCd: 0, climb: { on: false, s: 0 }, carrier: null, carrying: [], elig: false, still: 0,
      input: { f: 0, s: 0, t: 0, eject: false }, pend: { climb: false, lift: false }, bot: null, ghost: false
    };
  }
  function mkBot(rng) { return { mode: 'collect', tgt: -1, tt: 0, stk: 0, un: 0, ud: 1, rank: -1, s0: 0.2 }; }

  function createMatch(o) {
    var d0 = { mode: 'match', team: 'red', slot: 1, cfg: defaultCfg(), partners: true, opponents: true, difficulty: 1, seed: 1, hp: 'auto', autoplay: false, code: 'KAZ' };
    o = Object.assign(d0, o || {});
    if (o.mode === 'skills') { o.team = 'red'; o.slot = 1; o.partners = true; o.opponents = false; }
    var rng = mulberry(o.seed), skills = o.mode === 'skills';
    var s = {
      mode: o.mode, rng: rng, t: 0, phase: skills ? 'play' : 'count', cd: skills ? 0 : COUNT_T, clock: skills ? SKILLS_T : MATCH_T, settle: SETTLE_T,
      su: { red: 0, blue: 0 }, ext: 0, hp: { red: o.hp, blue: 'auto' }, sh: { red: { q: [], tmr: 0 }, blue: { q: [], tmr: 0 } },
      fx: [], evq: [], robots: [], spawned: 0, acc: 0, diff: o.difficulty, sk: { port: 0, su: 0, ext: 0, t: 0, started: false, done: false },
      brace: { red: mkBrace('red'), blue: mkBrace('blue') }, cdLast: 4, player: null
    };
    var B = { n: NB, x: new Float32Array(NB), y: new Float32Array(NB), vx: new Float32Array(NB), vy: new Float32Array(NB), st: new Uint8Array(NB), pc: new Uint8Array(NB) };
    B.st.fill(4); s.B = B;
    s.grid = { head: new Int32Array(72 * 72), next: new Int32Array(NB) };
    var id = 0, usedCodes = {}, humans = [], partnerN = 0;
    ['red', 'blue'].forEach(function (team) {
      for (var slot = 0; slot < 3; slot++) {
        var sd = o.slots ? o.slots[(team === 'red' ? 0 : 3) + slot] : null;
        var isP = sd ? sd.kind === 'human' : (team === o.team && slot === o.slot);
        if (sd && sd.kind === 'off') continue;
        if (skills && team === 'blue') continue;
        if (!isP && !sd) {
          if (skills && partnerN >= 2) continue;
          if (team === o.team ? !o.partners : !o.opponents) continue;
          if (skills) partnerN++;
        }
        var cfg = isP ? normCfg(sd ? sd.cfg : o.cfg) : normCfg(TPL[Math.floor(rng() * TPL.length)]);
        var code;
        if (isP) code = sd ? sd.code : o.code; else { do { code = CODES[Math.floor(rng() * CODES.length)]; } while (usedCodes[code]); usedCodes[code] = 1; }
        var r = mkRobot(id++, team, slot, cfg, isP && !o.autoplay, code);
        if (!isP || o.autoplay) r.bot = mkBot(rng);
        if (isP) {
          r.isPlayer = true;
          if (sd) { r.pid = sd.pid; r.pname = sd.name; r.dev = sd.dev; humans.push(r); }
          if (!s.player) s.player = r;
        }
        s.robots.push(r);
      }
    });
    s.humans = humans.length ? humans : (s.player ? [s.player] : []);
    return s;
  }

  /* ------------------------------------------------------------------ climbing */
  function dropRobot(s, r) {
    var b = s.brace[r.team], p = pipePt(b, r.climb.s);
    releaseCarried(s, r);
    r.climb.on = false; r.x = p.x + b.nx * (RR + 14); r.y = p.y + b.ny * (RR + 14); r.vx = r.vy = 0; r.still = 0;
  }
  function releaseCarried(s, r) {
    var b = s.brace[r.team];
    for (var i = 0; i < r.carrying.length; i++) {
      var o = r.carrying[i]; o.carrier = null; o.x = r.x + b.nx * (RR + 34); o.y = r.y + b.ny * (RR + 34); o.vx = o.vy = 0;
    }
    r.carrying.length = 0;
  }
  function tryAttach(s, r) {
    var b = s.brace[r.team];
    if (r.d.cl < 1 || r.carrier) return false;
    var t = ((r.x - b.a.x) * b.ux + (r.y - b.a.y) * b.uy) / b.L;
    if (t > 1 / 3 + 0.03 || t < -0.02) return false;
    t = clamp(t, 0.02, 1 / 3);
    var q = pipePt(b, t);
    if (Math.hypot(r.x - q.x, r.y - q.y) > 46) return false;
    for (var i = 0; i < s.robots.length; i++) { var o = s.robots[i]; if (o !== r && o.team === r.team && o.climb.on && Math.abs(o.climb.s - t) * b.L < 52) return false; }
    r.climb.on = true; r.climb.s = t; r.vx = r.vy = 0; r.still = 0; s.evq.push('attach');
    return true;
  }
  function tryLift(s, r) {
    if (!r.d.lift || r.carrying.length >= 1) return false;
    var best = null, bd = 85;
    for (var i = 0; i < s.robots.length; i++) {
      var o = s.robots[i];
      if (o === r || o.team !== r.team || o.climb.on || o.carrier || o.carrying.length) continue;
      var dd = Math.hypot(o.x - r.x, o.y - r.y); if (dd < bd) { bd = dd; best = o; }
    }
    if (!best) return false;
    best.carrier = r; r.carrying.push(best); best.elig = r.climb.s <= 1 / 3 + 1e-9; best.vx = best.vy = 0; s.evq.push('lift');
    return true;
  }
  function updateClimb(s, r, dt) {
    var b = s.brace[r.team], p = r.pend, play = s.phase === 'play';
    if (!play) { p.climb = p.lift = false; }
    if (r.carrier) { var c = r.carrier; r.x = c.x + b.nx * 30; r.y = c.y + b.ny * 30; r.th = c.th; r.vx = r.vy = 0; p.climb = false; p.lift = false; return; }
    if (r.climb.on) {
      if (p.climb) { p.climb = false; dropRobot(s, r); return; }
      if (p.lift) { p.lift = false; if (r.carrying.length) releaseCarried(s, r); else tryLift(s, r); }
      var f = play ? r.input.f : 0, ns = r.climb.s + f * r.d.vclimb * dt / b.L, gap = 52 / b.L;
      for (var i = 0; i < s.robots.length; i++) {
        var o = s.robots[i]; if (o === r || o.team !== r.team || !o.climb.on) continue;
        if (o.climb.s > r.climb.s) ns = Math.min(ns, o.climb.s - gap); else ns = Math.max(ns, o.climb.s + gap);
      }
      ns = clamp(ns, 0, sMax(r.d.cl));
      if (ns <= 0.012 && f < 0) { dropRobot(s, r); return; }
      r.still = (Math.abs(ns - r.climb.s) < 1e-6) ? r.still + dt : 0;
      r.climb.s = ns;
      var q = pipePt(b, ns); r.x = q.x + b.nx * 22; r.y = q.y + b.ny * 22; r.th = Math.atan2(-b.ny, -b.nx); r.vx = r.vy = 0;
      return;
    }
    if (p.lift) p.lift = false;
    if (p.climb) { p.climb = false; if (play) tryAttach(s, r); }
  }
  function climbInfo(s, r) {
    var o = { z: 0, mult: 0, supported: false, contact: false };
    var z;
    if (r.climb.on) { z = zoneOf(r.climb.s); o.z = z; o.mult = [0.1, 0.2, 0.3][z - 1]; return o; }
    if (r.carrier && r.carrier.climb.on) { z = zoneOf(r.carrier.climb.s); o.z = z; o.supported = true; o.mult = r.elig ? [0.1, 0.2, 0.3][z - 1] : 0; return o; }
    var b = s.brace[r.team], t = clamp(((r.x - b.a.x) * b.ux + (r.y - b.a.y) * b.uy) / b.L, 0, 1 / 3), q = pipePt(b, t);
    if (Math.hypot(r.x - q.x, r.y - q.y) <= 40) { o.contact = true; o.mult = 0.05; }
    return o;
  }

  /* ------------------------------------------------------------------ scoring */
  function scoreFor(s, team) {
    var mult = 1, partner = 0, z3 = 0, i, ci;
    for (i = 0; i < s.robots.length; i++) {
      var r = s.robots[i]; ci = climbInfo(s, r);
      if (ci.z === 3) z3++;
      if (r.team === team) { mult += ci.mult; if (ci.supported) partner += 25; }
    }
    var su = s.su[team], regional = Math.ceil(su * mult - 1e-9), ext = s.ext;
    var knock = (ext > s.su.red && ext > s.su.blue) ? 10 : 0, coop = z3 >= 6 ? 40 : z3 === 5 ? 25 : z3 === 4 ? 10 : 0;
    return { su: su, mult: mult, regional: regional, partner: partner, ext: ext, knock: knock, coop: coop, z3: z3, total: regional + partner + ext + knock + coop };
  }
  function skillsScore(s) {
    var cp = 0, zone = 0;
    s.robots.forEach(function (r) {
      if (r.team !== 'red') return;
      var ci = climbInfo(s, r), c = 0;
      if (ci.z > 0) c = [110, 130, 150][ci.z - 1]; else if (ci.contact) c = 50;
      cp += c; zone = Math.max(zone, ci.z);
    });
    var pts = s.sk.port + s.sk.su * 5 + s.sk.ext * 2 + cp, sec = Math.max(1, Math.ceil(s.sk.t - 1e-9));
    return { port: s.sk.port, su: s.sk.su, ext: s.sk.ext, climb: cp, zone: zone, pts: pts, sec: sec, ratio: pts / sec, score: Math.ceil(pts / sec - 1e-9) };
  }
  function skillsBoard(s) {
    var a = s.robots.filter(function (r) { return r.team === 'red'; }).map(function (r) {
      return { id: r.id, name: r.pname || (r === s.player ? 'YOU' : r.code), human: !!r.human, mine: r === s.player, goals: r.goals || 0 };
    });
    a.sort(function (x, y) { return y.goals - x.goals || x.id - y.id; });
    return a;
  }
  function stopRun(s) { if (s.mode === 'skills' && !s.sk.done) { s.sk.done = true; s.phase = 'done'; s.evq.push('end'); } }
  function press(s, what, r) { r = r || s.player; if (r) r.pend[what] = true; }

  /* ------------------------------------------------------------------ bots */
  function goTo(s, r, tx, ty, tth, ss) {
    var dx = tx - r.x, dy = ty - r.y, dist = Math.hypot(dx, dy), inp = r.input, d = r.d;
    var ax = dist > 0.001 ? dx / dist : 0, ay = dist > 0.001 ? dy / dist : 0, mag = Math.min(1, dist / 45), rx = 0, ry = 0;
    for (var i = 0; i < s.robots.length; i++) {
      var o = s.robots[i]; if (o === r || o.ghost) continue;
      var ex = r.x - o.x, ey = r.y - o.y, ed = Math.hypot(ex, ey);
      if (ed < 100 && ed > 0.1) { var w = (100 - ed) / 100; rx += ex / ed * w * 1.1; ry += ey / ed * w * 1.1; }
    }
    var vx = ax * mag + rx, vy = ay * mag + ry, vm = Math.hypot(vx, vy);
    if (vm > 1) { vx /= vm; vy /= vm; }
    var c = Math.cos(r.th), sn = Math.sin(r.th), lf = vx * c + vy * sn, ls = -vx * sn + vy * c, aerr = 0;
    if (d.mec) {
      var want = tth !== null ? tth : (vm > 0.15 ? Math.atan2(vy, vx) : r.th);
      var e = angDiff(want, r.th); aerr = Math.abs(e);
      inp.f = lf * ss; inp.s = ls * ss; inp.t = clamp(e * 3.5, -1, 1);
      if (tth !== null && dist < 90) { /* keep facing target pose while closing */ }
    } else {
      var dir = (dist > 16 || tth === null) ? Math.atan2(vy, vx) : tth;
      if (dist > 16 && vm < 0.05) dir = r.th;
      var e2 = angDiff(dir, r.th);
      aerr = tth !== null ? Math.abs(angDiff(tth, r.th)) : Math.abs(e2);
      inp.t = clamp(e2 * 3.2, -1, 1);
      inp.f = (dist > 16 && Math.abs(e2) < 1.1) ? Math.max(0, Math.cos(e2)) * Math.min(1, vm + 0.15) * ss : 0;
    }
    return { dist: dist, aerr: aerr };
  }
  function needTime(s, r) {
    var b = s.brace[r.team], st = sMax(r.d.cl) * b.L, s0 = (r.bot.s0 || 0.15) * b.L;
    return 9 + Math.max(0, st - s0) / r.d.vclimb + 4 + (r.d.lift ? 6 : 0);
  }
  function canScoreSU(r) {
    var su = SU[r.team];
    var xm = 8 + (r.d.shoot - 1) * 10;
    return r.x >= su.x0 - xm && r.x <= su.x1 + xm && r.y <= 107 + 28 * r.d.shoot && r.y >= 70 && Math.abs(angDiff(r.th, -Math.PI / 2)) < 0.6;
  }
  function botStep(s, r, dt) {
    var b = r.bot, d = r.d, ss = [0.42, 0.58, 0.75][s.diff], inp = r.input, B = s.B, rng = s.rng, i;
    inp.f = 0; inp.s = 0; inp.t = 0; inp.eject = false; r.intakeOn = true;
    if (s.phase !== 'play' || r.carrier) return;
    var br = s.brace[r.team], rem = s.clock, L = br.L, mates = s.robots.filter(function (o) { return o.team === r.team && o !== r; });
    if (b.rank < 0) {
      var cl = s.robots.filter(function (o) { return o.team === r.team && o.d.cl > 0; }).sort(function (a, c) { return c.d.cl - a.d.cl || a.slot - c.slot; });
      var rk = cl.indexOf(r); if (rk < 0) rk = 0;
      b.rank = rk; b.s0 = 0.11 + 0.085 * Math.max(0, Math.min(2, cl.length - 1 - rk));
    }
    if (r.climb.on) { b.mode = 'climb'; }
    else if (b.mode !== 'brace' && b.mode !== 'getlift' && b.mode !== 'park') {
      if (d.cl > 0) { if (rem <= needTime(s, r)) b.mode = 'brace'; }
      else {
        var lifter = mates.filter(function (o) { return o.d.lift && o.d.cl > 0; })[0];
        if (lifter && lifter.bot && rem <= needTime(s, lifter) + 2) b.mode = 'getlift';
        else if (rem <= 14) b.mode = 'park';
      }
    }
    var moving = true, g = null;
    if (b.mode === 'climb') {
      if (!r.climb.on) { b.mode = 'brace'; return; }
      var needy = mates.filter(function (o) { return o.d.cl === 0 && !o.carrier && o.bot && o.bot.mode === 'getlift'; })[0];
      if (d.lift && r.carrying.length === 0 && r.climb.s <= 1 / 3 && needy && Math.hypot(needy.x - r.x, needy.y - r.y) < 80) r.pend.lift = true;
      var anyNeedy = mates.some(function (o) { return o.d.cl === 0 && !o.carrier; });
      var wait = d.lift && r.carrying.length === 0 && anyNeedy && rem > (sMax(d.cl) - r.climb.s) * L / d.vclimb + 4;
      inp.f = wait ? 0 : 1; return;
    }
    if (b.mode === 'brace') {
      var P = pipePt(br, b.s0), tth = Math.atan2(-br.ny, -br.nx);
      g = goTo(s, r, P.x + br.nx * 30, P.y + br.ny * 30, tth, ss);
      if (g.dist < 16 && g.aerr < 0.35) { r.pend.climb = true; inp.f = 0; inp.s = 0; inp.t = 0; }
    } else if (b.mode === 'getlift') {
      var car = mates.filter(function (o) { return o.d.lift && o.climb.on && o.carrying.length === 0; })[0], tx, ty;
      if (car) { tx = car.x + br.nx * 64; ty = car.y + br.ny * 64; } else { var Q = pipePt(br, 0.12); tx = Q.x + br.nx * 110; ty = Q.y + br.ny * 110; }
      g = goTo(s, r, tx, ty, Math.atan2(-br.ny, -br.nx), ss * 0.8);
    } else if (b.mode === 'park') {
      var sp = 0.15 + 0.09 * r.slot, Pp = pipePt(br, sp);
      g = goTo(s, r, Pp.x + br.nx * 34, Pp.y + br.ny * 34, null, ss * 0.7);
      if (g.dist < 10) { inp.f = 0; inp.s = 0; inp.t = 0; moving = false; }
    } else if (b.mode === 'su') {
      var su = SU[r.team], cx = (su.x0 + su.x1) / 2 + (r.slot === 0 ? -26 : r.slot === 1 ? 26 : 0);
      g = goTo(s, r, cx, 100, -Math.PI / 2, ss);
      if (Math.abs(r.x - cx) < 16 && r.y < 125 && g.aerr < 0.3) {
        inp.f = 0; inp.s = 0; inp.eject = true; moving = false; inp.t = clamp(angDiff(-Math.PI / 2, r.th) * 3, -1, 1);
        if (r.held.length === 0) b.mode = 'collect';
      }
    } else if (b.mode === 'port') {
      var sh = SH[r.team], px = sh.face + sh.sgn * (RH + 24), pth = sh.sgn > 0 ? Math.PI : 0;
      g = goTo(s, r, px, 660, pth, ss);
      if (Math.abs(r.y - 660) < 12 && Math.abs(r.x - px) < 18 && g.aerr < 0.25) {
        inp.f = 0; inp.s = 0; inp.eject = true; moving = false; inp.t = clamp(angDiff(pth, r.th) * 3, -1, 1);
        if (r.held.length === 0) b.mode = 'collect';
      }
    } else { /* collect */
      b.tt -= dt;
      if (b.tgt < 0 || b.tt <= 0 || B.st[b.tgt] !== 0) {
        var bi = -1, bs = 1e9;
        for (i = 0; i < B.n; i++) {
          if (B.st[i] !== 0) continue; var bx = B.x[i], by = B.y[i];
          if (bx < 12 || bx > 688 || by > 688) continue;
          if (bx > ASM.x0 - 20 && bx < ASM.x1 + 20 && by < ASM.y1 + 22) continue;
          if ((bx < 100 || bx > 600) && by > 600) continue;
          var sc = Math.hypot(bx - r.x, by - r.y);
          for (var m = 0; m < mates.length; m++) { if (mates[m].bot && mates[m].bot.tgt === i) sc += 160; }
          if (sc < bs) { bs = sc; bi = i; }
        }
        b.tgt = bi; b.tt = 0.5;
      }
      var thr = Math.min(d.cap, (r.slot === 2 && s.mode !== 'skills') ? 6 : 8);
      if (r.held.length >= thr || (r.held.length > 0 && b.tgt < 0)) {
        b.mode = (r.slot === 2 && s.mode !== 'skills') ? 'port' : 'su'; b.tgt = -1;
      } else if (b.tgt >= 0) {
        g = goTo(s, r, B.x[b.tgt], B.y[b.tgt], null, ss);
      } else { moving = false; }
    }
    if (moving && g) {
      var sp2 = Math.hypot(r.vx, r.vy);
      if (sp2 < 8 && g.dist > 24 && b.mode !== 'brace') b.stk += dt; else b.stk = Math.max(0, b.stk - dt * 2);
      if (b.stk > 1.3) { b.un = 0.8; b.stk = 0; b.ud = rng() < 0.5 ? -1 : 1; b.tt = 0; }
    }
    if (b.un > 0) { b.un -= dt; inp.f = -0.9; inp.s = 0; inp.t = b.ud; }
  }

  /* ------------------------------------------------------------------ physics */
  function circleAABB(r, x0, y0, x1, y1) {
    var cx = clamp(r.x, x0, x1), cy = clamp(r.y, y0, y1), dx = r.x - cx, dy = r.y - cy, d2 = dx * dx + dy * dy;
    if (d2 < RR * RR) {
      var nx, ny, pen;
      if (d2 > 1e-6) { var d = Math.sqrt(d2); nx = dx / d; ny = dy / d; pen = RR - d; }
      else { var l = r.x - x0, rr = x1 - r.x, t = r.y - y0, bb = y1 - r.y, m = Math.min(l, rr, t, bb); if (m === l) { nx = -1; ny = 0; } else if (m === rr) { nx = 1; ny = 0; } else if (m === t) { nx = 0; ny = -1; } else { nx = 0; ny = 1; } pen = m + RR; }
      r.x += nx * pen; r.y += ny * pen;
      var vn = r.vx * nx + r.vy * ny; if (vn < 0) { r.vx -= vn * nx; r.vy -= vn * ny; }
    }
  }
  function stepRobots(s, dt) {
    var R = s.robots, i, j, play = s.phase === 'play';
    for (i = 0; i < R.length; i++) {
      var r = R[i];
      if (r.bot && !(s.mode === 'skills' && !s.sk.started)) botStep(s, r, dt); else if (!play) { r.input.f = r.input.s = r.input.t = 0; r.input.eject = false; }
      if (!play) { r.input.f = r.input.s = r.input.t = 0; r.input.eject = false; }
      updateClimb(s, r, dt);
      r.ghost = r.climb.on || !!r.carrier;
      if (r.ghost) continue;
      var d = r.d, f = r.input.f, sx = d.mec ? r.input.s : 0, tt = r.input.t;
      var m = Math.hypot(f, sx); if (m > 1) { f /= m; sx /= m; }
      var c = Math.cos(r.th), sn = Math.sin(r.th), tvx = (c * f - sn * sx) * d.vmax, tvy = (sn * f + c * sx) * d.vmax;
      var ax = tvx - r.vx, ay = tvy - r.vy, am = Math.hypot(ax, ay), lim = (300 / d.mass) * dt;
      if (am > lim) { ax *= lim / am; ay *= lim / am; }
      r.vx += ax; r.vy += ay;
      var tom = tt * 3.0, ao = tom - r.om, al = 14 * dt; r.om += clamp(ao, -al, al);
      r.th += r.om * dt; if (r.th > Math.PI) r.th -= 2 * Math.PI; else if (r.th < -Math.PI) r.th += 2 * Math.PI;
      r.x += r.vx * dt; r.y += r.vy * dt;
    }
    for (i = 0; i < R.length; i++) {
      var a = R[i]; if (a.ghost) continue;
      for (j = i + 1; j < R.length; j++) {
        var b = R[j]; if (b.ghost) continue;
        var dx = a.x - b.x, dy = a.y - b.y, dd = Math.hypot(dx, dy), md = 2 * RR;
        if (dd < md && dd > 1e-4) {
          var nx = dx / dd, ny = dy / dd, pen = md - dd, ia = 1 / a.d.mass, ib = 1 / b.d.mass, sm = ia + ib;
          a.x += nx * pen * ia / sm; a.y += ny * pen * ia / sm; b.x -= nx * pen * ib / sm; b.y -= ny * pen * ib / sm;
          var vn = (a.vx - b.vx) * nx + (a.vy - b.vy) * ny;
          if (vn < 0) { var jn = -(1.1) * vn / sm; a.vx += jn * nx * ia; a.vy += jn * ny * ia; b.vx -= jn * nx * ib; b.vy -= jn * ny * ib; }
        }
      }
    }
    for (i = 0; i < R.length; i++) {
      var q = R[i]; if (q.ghost) continue;
      circleAABB(q, ASM.x0, ASM.y0, ASM.x1, ASM.y1);
      circleAABB(q, SH.red.x0, SH.red.y0, SH.red.x1, SH.red.y1);
      circleAABB(q, SH.blue.x0, SH.blue.y0, SH.blue.x1, SH.blue.y1);
      if (q.x < RR) { q.x = RR; if (q.vx < 0) q.vx = 0; } else if (q.x > F - RR) { q.x = F - RR; if (q.vx > 0) q.vx = 0; }
      if (q.y < RR) { q.y = RR; if (q.vy < 0) q.vy = 0; } else if (q.y > F - RR) { q.y = F - RR; if (q.vy > 0) q.vy = 0; }
    }
  }

  function spawnBall(s, i) {
    var B = s.B, rng = s.rng, x = 294 + rng() * 112;
    B.st[i] = 0; B.x[i] = x; B.y[i] = 67 + rng() * 6; B.vx[i] = (x - 350) * 2.6 + (rng() - 0.5) * 120; B.vy[i] = 90 + rng() * 230;
  }
  function ballAABB(B, i, x0, y0, x1, y1) {
    var cx = clamp(B.x[i], x0, x1), cy = clamp(B.y[i], y0, y1), dx = B.x[i] - cx, dy = B.y[i] - cy, d2 = dx * dx + dy * dy;
    if (d2 < BR * BR) {
      var nx, ny, pen;
      if (d2 > 1e-6) { var d = Math.sqrt(d2); nx = dx / d; ny = dy / d; pen = BR - d; }
      else { var l = B.x[i] - x0, rr = x1 - B.x[i], t = B.y[i] - y0, bb = y1 - B.y[i], m = Math.min(l, rr, t, bb); if (m === l) { nx = -1; ny = 0; } else if (m === rr) { nx = 1; ny = 0; } else if (m === t) { nx = 0; ny = -1; } else { nx = 0; ny = 1; } pen = m + BR; }
      B.x[i] += nx * pen; B.y[i] += ny * pen;
      var vn = B.vx[i] * nx + B.vy[i] * ny; if (vn < 0) { B.vx[i] -= 1.5 * vn * nx; B.vy[i] -= 1.5 * vn * ny; }
    }
  }
  function stepBalls(s, dt) {
    var B = s.B, n = B.n, i, play = s.phase === 'play';
    if (play && (s.mode !== 'skills' || s.sk.started) && s.spawned < NB) {
      s.acc += dt * 190; var k = Math.floor(s.acc); s.acc -= k;
      while (k-- > 0 && s.spawned < NB) { spawnBall(s, s.spawned); s.spawned++; }
    }
    var fr = Math.exp(-1.15 * dt), g = s.grid, head = g.head, next = g.next;
    head.fill(-1);
    for (i = 0; i < n; i++) {
      if (B.st[i] !== 0) continue;
      B.x[i] += B.vx[i] * dt; B.y[i] += B.vy[i] * dt; B.vx[i] *= fr; B.vy[i] *= fr;
      var x = B.x[i], y = B.y[i];
      if (x < BR) { B.x[i] = BR; B.vx[i] = -B.vx[i] * 0.5; } else if (x > F - BR) { B.x[i] = F - BR; B.vx[i] = -B.vx[i] * 0.5; }
      if (y < BR) { B.y[i] = BR; B.vy[i] = -B.vy[i] * 0.5; } else if (y > F - BR) { B.y[i] = F - BR; B.vy[i] = -B.vy[i] * 0.5; }
      // fire shield port
      var absorbed = false;
      for (var t = 0; t < 2; t++) {
        var team = t ? 'blue' : 'red', sh = SH[team];
        if (B.y[i] >= sh.py0 && B.y[i] <= sh.py1 && (sh.sgn > 0 ? (B.x[i] <= sh.face + BR + 1 && B.x[i] >= sh.face - 20) : (B.x[i] >= sh.face - BR - 1 && B.x[i] <= sh.face + 20))) {
          B.st[i] = 2; sh_q(s, team, i); B.x[i] = -80; B.y[i] = -80; B.vx[i] = B.vy[i] = 0; absorbed = true;
          if (!B.pc[i]) { B.pc[i] = 1; if (s.mode === 'skills' && team === 'red') s.sk.port++; }
          break;
        }
      }
      if (absorbed) continue;
      ballAABB(B, i, ASM.x0, ASM.y0, ASM.x1, ASM.y1);
      ballAABB(B, i, SH.red.x0, SH.red.y0, SH.red.x1, SH.red.y1);
      ballAABB(B, i, SH.blue.x0, SH.blue.y0, SH.blue.x1, SH.blue.y1);
    }
    // ball-ball
    for (var pass = 0; pass < 3; pass++) {
      if (pass === 0) {
        head.fill(-1);
        for (i = 0; i < n; i++) { if (B.st[i] !== 0) continue; var cx = clamp((B.x[i] / 10) | 0, 0, 70), cy = clamp((B.y[i] / 10) | 0, 0, 70), c = cy * 72 + cx; next[i] = head[c]; head[c] = i; }
      }
      for (i = 0; i < n; i++) {
        if (B.st[i] !== 0) continue;
        var gx = clamp((B.x[i] / 10) | 0, 0, 70), gy = clamp((B.y[i] / 10) | 0, 0, 70);
        for (var oy = -1; oy <= 1; oy++) {
          var yy = gy + oy; if (yy < 0 || yy > 70) continue;
          for (var ox = -1; ox <= 1; ox++) {
            var xx = gx + ox; if (xx < 0 || xx > 70) continue;
            for (var j = head[yy * 72 + xx]; j >= 0; j = next[j]) {
              if (j <= i) continue;
              var dx = B.x[i] - B.x[j], dy = B.y[i] - B.y[j], d2 = dx * dx + dy * dy;
              if (d2 < 4 * BR * BR && d2 > 1e-8) {
                var d = Math.sqrt(d2), nx = dx / d, ny = dy / d, ov = (2 * BR - d) * 0.5;
                B.x[i] += nx * ov; B.y[i] += ny * ov; B.x[j] -= nx * ov; B.y[j] -= ny * ov;
                var vn = (B.vx[i] - B.vx[j]) * nx + (B.vy[i] - B.vy[j]) * ny;
                if (vn < 0) { var im = -0.65 * vn; B.vx[i] += im * nx; B.vy[i] += im * ny; B.vx[j] -= im * nx; B.vy[j] -= im * ny; }
              }
            }
          }
        }
      }
    }
    // robots vs balls
    for (var ri = 0; ri < s.robots.length; ri++) {
      var r = s.robots[ri]; if (r.ghost) continue;
      var co = Math.cos(r.th), sn = Math.sin(r.th), iw2 = r.d.iw / 2;
      var act = r.intakeOn && !r.input.eject && r.held.length < r.d.cap && play;
      if (r.inCd > 0) { r.inCd -= dt; act = false; }
      for (i = 0; i < n; i++) {
        if (B.st[i] !== 0) continue;
        var ddx = B.x[i] - r.x, ddy = B.y[i] - r.y; if (ddx * ddx + ddy * ddy > 2500) continue;
        var lx = ddx * co + ddy * sn, ly = -ddx * sn + ddy * co;
        if (act && lx >= 8 && lx <= RH + BR + 3 && Math.abs(ly) <= iw2) {
          B.st[i] = 1; r.held.push(i); B.x[i] = -50; B.y[i] = -50; B.vx[i] = B.vy[i] = 0;
          r.inCd = 0.16; act = false;
          continue;
        }
        var qx = clamp(lx, -RH, RH), qy = clamp(ly, -RH, RH), ex = lx - qx, ey = ly - qy, e2 = ex * ex + ey * ey;
        if (e2 < BR * BR) {
          var nxl, nyl, pen;
          if (e2 > 1e-6) { var dd = Math.sqrt(e2); nxl = ex / dd; nyl = ey / dd; pen = BR - dd; }
          else { var ox2 = RH - Math.abs(lx), oy2 = RH - Math.abs(ly); if (ox2 < oy2) { nxl = lx > 0 ? 1 : -1; nyl = 0; pen = ox2 + BR; } else { nxl = 0; nyl = ly > 0 ? 1 : -1; pen = oy2 + BR; } }
          var wx = nxl * co - nyl * sn, wy = nxl * sn + nyl * co;
          B.x[i] += wx * pen; B.y[i] += wy * pen;
          var vn2 = (B.vx[i] - r.vx) * wx + (B.vy[i] - r.vy) * wy;
          if (vn2 < 0) { B.vx[i] -= 1.25 * vn2 * wx; B.vy[i] -= 1.25 * vn2 * wy; }
        }
      }
    }
  }
  function sh_q(s, team, i) { s.sh[team].q.push(i); }

  function stepEject(s, dt) {
    var B = s.B, play = s.phase === 'play';
    for (var i = 0; i < s.robots.length; i++) {
      var r = s.robots[i]; if (r.ejCd > 0) r.ejCd -= dt;
      if (!play || r.ghost || !r.input.eject || r.ejCd > 0 || r.held.length === 0) continue;
      var idx = r.held.pop();
      if (canScoreSU(r)) {
        r.ejCd = 1 / r.d.rate;
        B.st[idx] = 3; s.su[r.team]++; r.goals++; if (s.mode === 'skills') s.sk.su++;
        var su = SU[r.team];
        s.fx.push({ x: r.x + Math.cos(r.th) * 28, y: r.y + Math.sin(r.th) * 28, tx: (su.x0 + su.x1) / 2 + (s.rng() - 0.5) * 60, ty: 30, t: 0, d: 0.34 - 0.04 * r.d.shoot });
        s.evq.push('score');
      } else {
        r.ejCd = Math.min(0.25, 0.6 / r.d.rate);
        var c = Math.cos(r.th), sn = Math.sin(r.th), lat = (s.rng() - 0.5) * 20;
        B.st[idx] = 0; B.x[idx] = r.x + c * (RH + BR + 3); B.y[idx] = r.y + sn * (RH + BR + 3);
        B.vx[idx] = r.vx + c * (70 + 40 * r.d.shoot) - sn * lat; B.vy[idx] = r.vy + sn * (70 + 40 * r.d.shoot) + c * lat;
      }
    }
  }
  function stepHP(s, dt) {
    var B = s.B, play = s.phase === 'play';
    ['red', 'blue'].forEach(function (team) {
      var h = s.sh[team]; if (h.tmr > 0) h.tmr -= dt;
      if (!play || h.tmr > 0 || !h.q.length) return;
      if (s.mode === 'skills' && team === 'blue') return;
      var mode = s.hp[team]; if (mode === 'auto') mode = (s.mode !== 'skills' && s.clock <= 45) ? 'ext' : 'chute';
      var idx = h.q.shift(), sh = SH[team];
      if (mode === 'ext') { B.st[idx] = 3; s.ext++; if (s.mode === 'skills') s.sk.ext++; h.tmr = 0.9; s.fx.push({ x: sh.ex, y: 640, tx: 350, ty: 30, t: 0, d: 0.5 }); }
      else { B.st[idx] = 0; B.x[idx] = sh.ex + (s.rng() - 0.5) * 22; B.y[idx] = sh.ey; B.vx[idx] = (s.rng() - 0.5) * 20; B.vy[idx] = -60 - s.rng() * 30; h.tmr = 1.3; }
    });
  }

  function step(s, dt) {
    if (s.phase === 'done') return;
    s.t += dt;
    var i;
    if (s.phase === 'count') {
      s.cd -= dt;
      var cc = Math.ceil(s.cd); if (cc !== s.cdLast && cc > 0) { s.cdLast = cc; s.evq.push('tick'); }
      if (s.cd <= 0) { s.phase = 'play'; s.evq.push('go'); }
    }
    stepRobots(s, dt);
    stepBalls(s, dt);
    stepEject(s, dt);
    stepHP(s, dt);
    for (i = s.fx.length - 1; i >= 0; i--) { s.fx[i].t += dt; if (s.fx[i].t >= s.fx[i].d) s.fx.splice(i, 1); }
    if (s.phase === 'play') {
      if (s.mode === 'skills') {
        var hs = s.humans && s.humans.length ? s.humans : [s.player];
        if (!s.sk.started && hs.some(function (h) { return Math.hypot(h.vx, h.vy) > 3 || h.climb.on; })) s.sk.started = true;
        if (s.sk.started) { s.clock -= dt; s.sk.t += dt; }
        var reds = s.robots.filter(function (r) { return r.team === 'red'; });
        if (s.sk.started && reds.length && reds.every(function (r) { return r.carrier || (r.climb.on && r.still >= 2); })) stopRun(s);
        if (s.clock <= 0) { s.clock = 0; s.sk.t = SKILLS_T; stopRun(s); }
      } else {
        s.clock -= dt;
        if (s.clock <= 0) { s.clock = 0; s.phase = 'settle'; s.evq.push('end'); }
      }
    } else if (s.phase === 'settle') {
      s.settle -= dt; if (s.settle <= 0) s.phase = 'done';
    }
  }

  return {
    F: F, BR: BR, RH: RH, RR: RR, MATCH_T: MATCH_T, SKILLS_T: SKILLS_T, NB: NB, ASM: ASM, SU: SU, EXT: EXT, SH: SH, STARTY: STARTY,
    createMatch: createMatch, step: step, press: press, stopRun: stopRun, scoreFor: scoreFor, skillsScore: skillsScore, skillsBoard: skillsBoard, climbInfo: climbInfo,
    defaultCfg: defaultCfg, normCfg: normCfg, derive: derive, CAPS: CAPS, RATES: RATES, pipePt: pipePt, zoneOf: zoneOf, sMax: sMax, canScoreSU: canScoreSU, mulberry: mulberry
  };
})();



(function () {
  'use strict';
  var $ = function (i) { return document.getElementById(i); };
  var RED = '#ea5b52', BLUE = '#4f8fff', EMBER = '#ff8a3c';

  /* ---------- language, storage ---------- */
  var lang = 'ru';
  try { var sl = localStorage.getItem('fgc.lang'); if (sl === 'en' || sl === 'ru') lang = sl; } catch (e) { }
  function L(ru, en) { return lang === 'ru' ? ru : en; }
  var cfg = { code: 'KAZ', robot: FGC.defaultCfg(), team: 'red', slot: 1, diff: 1, partners: true, hp: 'auto' };
  try {
    var c0 = JSON.parse(localStorage.getItem('fgc.cfg') || 'null');
    if (c0 && c0.robot) { cfg = Object.assign(cfg, c0); cfg.robot = FGC.normCfg(c0.robot); }
  } catch (e) { }
  function saveCfg() { try { localStorage.setItem('fgc.cfg', JSON.stringify(cfg)); } catch (e) { } }
  var rec = { match: { played: 0, wins: 0, best: 0, margin: 0 }, practice: { runs: 0, best: 0 }, skills: { runs: 0, best: 0, ratio: 0 } };
  try { var r0 = JSON.parse(localStorage.getItem('fgc.rec') || 'null'); if (r0) rec = Object.assign(rec, r0); } catch (e) { }
  function saveRec() { try { localStorage.setItem('fgc.rec', JSON.stringify(rec)); } catch (e) { } }
  var muted = false; try { muted = localStorage.getItem('fgc.mute') === '1'; } catch (e) { }

  /* ---------- sound ---------- */
  var AC = null, lastScoreBeep = 0;
  function beep(f, d, type, v) {
    if (muted) return;
    try {
      if (!AC) AC = new (window.AudioContext || window.webkitAudioContext)();
      if (AC.state === 'suspended') AC.resume();
      var o = AC.createOscillator(), g = AC.createGain(), t = AC.currentTime, vol = v || 0.05;
      o.type = type || 'square'; o.frequency.value = f; o.connect(g); g.connect(AC.destination);
      g.gain.setValueAtTime(vol, t); g.gain.exponentialRampToValueAtTime(0.0001, t + d); o.start(t); o.stop(t + d);
    } catch (e) { }
  }

  /* ---------- screens ---------- */
  var cur = 'menu';
  function show(name) {
    ['menu', 'config', 'rules', 'records', 'controls', 'local', 'game'].forEach(function (n) { $('scr-' + n).hidden = n !== name; });
    $('topbar').hidden = name === 'game';
    cur = name;
    document.querySelector('main').scrollTop = 0;
    if (name === 'config') renderConfig();
    kbRebind = null; padRebind = null;
    if (name === 'records') renderRecords();
    if (name === 'controls') renderControls();
    if (name === 'local') renderLocal();
    if (name === 'rules') renderRulesKeys();
    if (name === 'menu') renderMenuSum();
    resize();
  }
  function renderMenuSum() {
    var r = cfg.robot;
    $('menu-sum').textContent = cfg.code + ' · ' + r.rpm + ' RPM · ' + L(cfg.team === 'red' ? 'красный' : 'синий', cfg.team) + L(', позиция ', ', slot ') + (cfg.slot + 1);
  }
  function refreshAll() {
    document.documentElement.lang = lang;
    $('lng').textContent = lang === 'ru' ? 'RU · en' : 'ru · EN';
    $('snd').textContent = muted ? L('ЗВУК ВЫКЛ', 'SOUND OFF') : L('ЗВУК ВКЛ', 'SOUND ON');
    renderMenuSum(); buildPresets(); if (cur === 'config') renderConfig(); if (cur === 'records') renderRecords(); if (cur === 'controls') renderControls(); if (cur === 'local') renderLocal(); renderRulesKeys(); buildBar();
  }

  /* ---------- config ---------- */
  var PRESETS = [
    { ru: 'Баланс', en: 'Balanced', c: { drive: 'tank', rpm: 400, intake: 2, hopper: 2, transfer: 2, shooter: 2, climb: 2, lift: 0 } },
    { ru: 'Сборщик', en: 'Collector', c: { drive: 'tank', rpm: 400, intake: 3, hopper: 4, transfer: 3, shooter: 3, climb: 0, lift: 0 } },
    { ru: 'Бункер 60', en: 'Big hopper', c: { drive: 'tank', rpm: 350, intake: 3, hopper: 5, transfer: 3, shooter: 2, climb: 0, lift: 0 } },
    { ru: 'Стрелок', en: 'Shooter', c: { drive: 'tank', rpm: 400, intake: 2, hopper: 3, transfer: 5, shooter: 5, climb: 0, lift: 0 } },
    { ru: 'Альпинист', en: 'Climber', c: { drive: 'tank', rpm: 350, intake: 2, hopper: 2, transfer: 2, shooter: 2, climb: 3, lift: 0 } },
    { ru: 'Подъём партнёра', en: 'Lifter', c: { drive: 'tank', rpm: 350, intake: 2, hopper: 2, transfer: 2, shooter: 2, climb: 2, lift: 1 } },
    { ru: 'Спринтер', en: 'Sprinter', c: { drive: 'tank', rpm: 500, intake: 2, hopper: 1, transfer: 2, shooter: 2, climb: 1, lift: 0 } }
  ];
  function buildPresets() {
    var box = $('presets'); box.innerHTML = '';
    PRESETS.forEach(function (p) {
      var b = document.createElement('button'); b.type = 'button'; b.className = 'btn sm'; b.textContent = L(p.ru, p.en);
      b.onclick = function () { cfg.robot = Object.assign({}, p.c); saveCfg(); renderConfig(); };
      box.appendChild(b);
    });
  }
  var SL = { 'r-rpm': 'rpm', 'r-intake': 'intake', 'r-hopper': 'hopper', 'r-transfer': 'transfer', 'r-shooter': 'shooter', 'r-climb': 'climb', 'r-lift': 'lift' };
  function renderConfig() {
    var r = cfg.robot, d = FGC.derive(r);
    $('cfg-code').value = cfg.code;
    Object.keys(SL).forEach(function (id) { $(id).value = r[SL[id]]; });
    $('o-rpm').textContent = r.rpm + ' RPM'; $('o-intake').textContent = d.iw + ' cm'; $('o-hopper').textContent = d.cap;
    $('o-transfer').textContent = d.rate + L('/с', '/s'); $('o-shooter').textContent = 'Lv ' + r.shooter;
    $('o-climb').textContent = r.climb ? 'Zone ' + r.climb : L('нет', 'none'); $('o-lift').textContent = r.lift ? L('да', 'yes') : L('нет', 'no');
    $('stats').innerHTML = [
      [L('Макс. скорость', 'Top speed'), Math.round(d.vmax) + ' cm/s'], [L('Скорость подъёма', 'Climb speed'), d.cl ? d.vclimb + ' cm/s' : '—'],
      [L('Ширина захвата', 'Intake width'), d.iw + ' cm'], [L('Бункер', 'Hopper'), d.cap + L(' мячей', ' balls')],
      [L('Подача', 'Transfer'), d.rate + L(' мяч/с', ' balls/s')], [L('Дальность броска', 'Shooter range'), (47 + 28 * r.shooter) + ' cm'],
      [L('Достаёт до', 'Reaches'), d.cl ? 'Zone ' + d.cl : 'Contact'], [L('Масса', 'Mass'), d.mass.toFixed(2) + ' ×']
    ].map(function (a) { return '<div><span>' + a[0] + '</span><b>' + a[1] + '</b></div>'; }).join('');
    Array.prototype.forEach.call(document.querySelectorAll('.seg[data-k]'), function (seg) {
      var k = seg.getAttribute('data-k'), val = String(cfg[k]);
      Array.prototype.forEach.call(seg.children, function (b) { b.setAttribute('aria-pressed', b.getAttribute('data-v') === val ? 'true' : 'false'); });
    });
  }
  function initConfig() {
    Object.keys(SL).forEach(function (id) {
      $(id).addEventListener('input', function () {
        var key = SL[id], old = cfg.robot[key], v = parseInt(this.value, 10);
        cfg.robot[key] = v;
        saveCfg(); renderConfig();
      });
    });
    $('cfg-code').addEventListener('input', function () { cfg.code = this.value.toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 3) || 'KAZ'; saveCfg(); });
    Array.prototype.forEach.call(document.querySelectorAll('.seg[data-k]'), function (seg) {
      seg.addEventListener('click', function (e) {
        var b = e.target.closest('button'); if (!b) return;
        var k = seg.getAttribute('data-k'), v = b.getAttribute('data-v');
        if (k === 'drive') cfg.robot.drive = v;
        else if (k === 'slot' || k === 'diff') cfg[k] = parseInt(v, 10);
        else if (k === 'partners') cfg.partners = v === 'true';
        else cfg[k] = v;
        saveCfg(); renderConfig();
      });
    });
  }

  /* ---------- controls ---------- */
  var ACT = [
    ['fwd', 'Вперёд', 'Forward'], ['back', 'Назад', 'Back'], ['left', 'Поворот влево', 'Turn left'], ['right', 'Поворот вправо', 'Turn right'],
    ['eject', 'Бросок', 'Eject'], ['intake', 'Захват вкл / выкл', 'Intake on / off'], ['climb', 'Взяться за трубу', 'Grab pipe'],
    ['lift', 'Поднять партнёра', 'Lift partner'], ['hp', 'Режим игрока-человека', 'Human player mode'], ['stop', 'Skills: закончить забег', 'Skills: end run'], ['pause', 'Пауза', 'Pause']
  ];
  var RDESC = {
    fwd: ['Вперёд (на трубе: вверх)', 'Forward (on the pipe: up)'], back: ['Назад (на трубе: вниз)', 'Back (on the pipe: down)'],
    left: ['Поворот влево', 'Turn left'], right: ['Поворот вправо', 'Turn right'],
    eject: ['Бросок: в Suppression Unit, если стоишь под ним лицом к нему, иначе мяч выкатывается (так кормят порт Fire Shield)', 'Eject: scores into the Suppression Unit when you face it from below, otherwise the ball rolls out (this feeds the Fire Shield port)'],
    intake: ['Захват вкл / выкл', 'Intake on / off'], climb: ['Взяться за трубу в Zone 1 / отпустить', 'Grab the pipe in Zone 1 / release'],
    lift: ['Поднять союзника рядом / опустить', 'Lift a nearby teammate / put down'], hp: ['Режим игрока-человека', 'Human player mode'],
    stop: ['Skills: закончить забег', 'Skills: end the run'], pause: ['Пауза', 'Pause']
  };
  var KB_DEF = { fwd: ['KeyW', 'ArrowUp'], back: ['KeyS', 'ArrowDown'], left: ['KeyA', 'ArrowLeft'], right: ['KeyD', 'ArrowRight'], eject: ['Space', ''], intake: ['KeyI', ''], climb: ['KeyC', ''], lift: ['KeyL', ''], hp: ['KeyH', ''], stop: ['Enter', ''], pause: ['KeyP', 'Escape'] };
  var PAD_ACT = ['eject', 'intake', 'climb', 'lift', 'hp', 'stop', 'pause'];
  var PAD_DEF = { eject: [7, 5], intake: [0, -1], climb: [3, -1], lift: [2, -1], hp: [4, -1], stop: [8, -1], pause: [9, -1] };
  var PADN = ['✕ Cross', '○ Circle', '□ Square', '△ Triangle', 'L1', 'R1', 'L2', 'R2', 'Create', 'Options', 'L3', 'R3', 'D-pad ↑', 'D-pad ↓', 'D-pad ←', 'D-pad →', 'PS', 'Touchpad'];
  function copy(o) { return JSON.parse(JSON.stringify(o)); }
  function defCtl() { return { kb: copy(KB_DEF), pad: { map: copy(PAD_DEF), scheme: 'arcade', dz: 14, turn: 100, inv: false } }; }
  var ctl = defCtl(), kbRebind = null, padRebind = null, padBtnPrev = [];
  try {
    var c1 = JSON.parse(localStorage.getItem('fgc.ctl') || 'null');
    if (c1) {
      if (c1.kb) ACT.forEach(function (a) { var v = c1.kb[a[0]]; if (Array.isArray(v)) ctl.kb[a[0]] = [String(v[0] || ''), String(v[1] || '')]; });
      if (c1.pad) {
        var pm = c1.pad.map || {};
        PAD_ACT.forEach(function (a) { var v = pm[a]; if (Array.isArray(v)) ctl.pad.map[a] = [isFinite(v[0]) && v[0] !== null ? +v[0] : -1, isFinite(v[1]) && v[1] !== null ? +v[1] : -1]; });
        if (['arcade', 'single', 'tank'].indexOf(c1.pad.scheme) >= 0) ctl.pad.scheme = c1.pad.scheme;
        if (isFinite(c1.pad.dz) && c1.pad.dz !== null) ctl.pad.dz = Math.max(0, Math.min(40, +c1.pad.dz));
        if (isFinite(c1.pad.turn) && c1.pad.turn !== null) ctl.pad.turn = Math.max(50, Math.min(150, +c1.pad.turn));
        ctl.pad.inv = !!c1.pad.inv;
      }
    }
  } catch (e) { }
  function saveCtl() { try { localStorage.setItem('fgc.ctl', JSON.stringify(ctl)); } catch (e) { } }
  function is(code, a) { return ctl.kb[a].indexOf(code) >= 0; }
  function held(a) { var l = ctl.kb[a]; for (var i = 0; i < l.length; i++) if (l[i] && keys[l[i]]) return 1; return 0; }
  function isBound(code) { for (var i = 0; i < ACT.length; i++) if (is(code, ACT[i][0])) return true; return false; }
  function setKey(a, i, code) {
    ACT.forEach(function (x) { for (var j = 0; j < 2; j++) if (ctl.kb[x[0]][j] === code) ctl.kb[x[0]][j] = ''; });
    ctl.kb[a][i] = code;
  }
  var KN = { ArrowUp: '↑', ArrowDown: '↓', ArrowLeft: '←', ArrowRight: '→', Space: 'Space', Enter: 'Enter', Escape: 'Esc', ShiftLeft: 'Shift L', ShiftRight: 'Shift R', ControlLeft: 'Ctrl L', ControlRight: 'Ctrl R', AltLeft: 'Alt L', AltRight: 'Alt R', Tab: 'Tab', Backquote: '`', Minus: '-', Equal: '=', Comma: ',', Period: '.', Slash: '/', Semicolon: ';', Quote: "'", BracketLeft: '[', BracketRight: ']', Backslash: '\\' };
  function keyLabel(c) {
    if (!c) return '—';
    if (c.indexOf('Key') === 0) return c.slice(3);
    if (c.indexOf('Digit') === 0) return c.slice(5);
    if (c.indexOf('Numpad') === 0) return 'Num ' + c.slice(6);
    return KN[c] || c;
  }
  function kbs(a) { var l = ctl.kb[a].filter(Boolean).map(keyLabel); return l.length ? l.join(' / ') : '—'; }
  function padLabel(i) { return i < 0 ? '—' : (PADN[i] || L('Кнопка ', 'Button ') + i); }
  function actName(id) { for (var i = 0; i < ACT.length; i++) if (ACT[i][0] === id) return L(ACT[i][1], ACT[i][2]); return id; }
  function keyHint() {
    var k = function (a) { return '<kbd>' + kbs(a) + '</kbd>'; };
    return k('fwd') + ' / ' + k('back') + L(' вперёд / назад', ' forward / back') + ' · ' + k('left') + ' / ' + k('right') + L(' поворот', ' turn') + ' · ' + k('eject') + L(' бросок', ' eject') +
      ' · ' + k('intake') + L(' захват', ' intake') + ' · ' + k('climb') + L(' подъём', ' climb') + ' · ' + k('lift') + L(' партнёр', ' lift') + ' · ' + k('hp') + L(' игрок-человек', ' human player') + ' · ' + k('pause') + L(' пауза', ' pause');
  }
  function renderRulesKeys() {
    var t = $('rules-keys'); if (!t) return;
    t.innerHTML = ACT.map(function (a) {
      return '<tr><td>' + ctl.kb[a[0]].filter(Boolean).map(function (c) { return '<kbd>' + keyLabel(c) + '</kbd>'; }).join(' ') + '</td><td>' + L(RDESC[a[0]][0], RDESC[a[0]][1]) + '</td></tr>';
    }).join('');
  }
  function renderControls() {
    $('kb-list').innerHTML = ACT.map(function (a) {
      return '<div class="keyrow"><span>' + L(a[1], a[2]) + '</span>' + [0, 1].map(function (i) {
        var w = kbRebind && kbRebind.a === a[0] && kbRebind.i === i;
        return '<button type="button" class="keybtn' + (w ? ' wait' : '') + '" data-ka="' + a[0] + '" data-ki="' + i + '">' + (w ? L('нажмите…', 'press…') : keyLabel(ctl.kb[a[0]][i])) + '</button>';
      }).join('') + '</div>';
    }).join('');
    $('pad-list').innerHTML = PAD_ACT.map(function (id) {
      return '<div class="keyrow"><span>' + actName(id) + '</span>' + [0, 1].map(function (i) {
        var w = padRebind && padRebind.a === id && padRebind.i === i;
        return '<button type="button" class="keybtn' + (w ? ' wait' : '') + '" data-pa="' + id + '" data-pi="' + i + '">' + (w ? L('нажмите кнопку…', 'press a button…') : padLabel(ctl.pad.map[id][i])) + '</button>';
      }).join('') + '</div>';
    }).join('');
    Array.prototype.forEach.call(document.querySelectorAll('.seg[data-pk]'), function (seg) {
      var k = seg.getAttribute('data-pk'), val = k === 'scheme' ? ctl.pad.scheme : String(ctl.pad.inv);
      Array.prototype.forEach.call(seg.children, function (b) { b.setAttribute('aria-pressed', b.getAttribute('data-v') === val ? 'true' : 'false'); });
    });
    $('p-dz').value = ctl.pad.dz; $('o-dz').textContent = ctl.pad.dz + '%'; $('p-turn').value = ctl.pad.turn; $('o-turn').textContent = ctl.pad.turn + '%';
    var notes = {
      arcade: L('Левый стик: вперёд и назад. Правый стик: поворот.', 'Left stick: forward and back. Right stick: turn.'),
      single: L('Левый стик: движение и поворот одновременно.', 'Left stick: drive and turn together.'),
      tank: L('Два стика: левый управляет левым бортом, правый правым.', 'Two sticks: left drives the left side, right drives the right side.')
    };
    $('scheme-note').textContent = notes[ctl.pad.scheme];
    padPoll();
  }
  function padPoll() {
    var g = getPad(), st = $('pad-status'), txt, i;
    if (!g) {
      padBtnPrev = [];
      txt = L('Геймпад не найден. Подключите DualSense по USB или Bluetooth и нажмите любую кнопку.', 'No gamepad found. Connect a DualSense over USB or Bluetooth and press any button.');
      if (st._t !== txt) { st.textContent = txt; st._t = txt; st.className = 'pad-status'; }
      return;
    }
    var pressed = [], names = [];
    for (i = 0; i < g.buttons.length; i++) { pressed[i] = padBtn(g, i); if (pressed[i]) names.push(padLabel(i)); }
    var hit = -1;
    if (padRebind) for (i = 0; i < pressed.length; i++) if (pressed[i] && !padBtnPrev[i]) { hit = i; break; }
    padBtnPrev = pressed;
    if (hit >= 0) { ctl.pad.map[padRebind.a][padRebind.i] = hit; padRebind = null; saveCtl(); renderControls(); return; }
    txt = L('Подключён: ', 'Connected: ') + String(g.id).replace(/\s*\(.*$/, '').slice(0, 40) + (g.mapping === 'standard' ? '' : L(' · нестандартная раскладка, кнопки могут отличаться', ' · non-standard mapping, buttons may differ')) + '\n' + L('Нажато: ', 'Pressed: ') + (names.join(', ') || '—');
    if (st._t !== txt) { st.textContent = txt; st._t = txt; st.className = 'pad-status on'; }
    var sl = $('sv-l').firstElementChild.style, sr = $('sv-r').firstElementChild.style;
    sl.transform = 'translate(' + (g.axes[0] || 0) * 28 + 'px,' + (g.axes[1] || 0) * 28 + 'px)';
    sr.transform = 'translate(' + (g.axes[2] || 0) * 28 + 'px,' + (g.axes[3] || 0) * 28 + 'px)';
  }
  function initControls() {
    $('kb-list').addEventListener('click', function (e) {
      var b = e.target.closest('.keybtn'); if (!b) return;
      kbRebind = { a: b.getAttribute('data-ka'), i: +b.getAttribute('data-ki') }; padRebind = null; renderControls();
    });
    $('pad-list').addEventListener('click', function (e) {
      var b = e.target.closest('.keybtn'); if (!b) return;
      padRebind = { a: b.getAttribute('data-pa'), i: +b.getAttribute('data-pi') }; kbRebind = null; renderControls();
    });
    $('kb-reset').onclick = function () { ctl.kb = defCtl().kb; kbRebind = null; saveCtl(); renderControls(); };
    $('pad-reset').onclick = function () { ctl.pad = defCtl().pad; padRebind = null; saveCtl(); renderControls(); };
    $('p-dz').addEventListener('input', function () { ctl.pad.dz = parseInt(this.value, 10); saveCtl(); $('o-dz').textContent = ctl.pad.dz + '%'; });
    $('p-turn').addEventListener('input', function () { ctl.pad.turn = parseInt(this.value, 10); saveCtl(); $('o-turn').textContent = ctl.pad.turn + '%'; });
    Array.prototype.forEach.call(document.querySelectorAll('.seg[data-pk]'), function (seg) {
      seg.addEventListener('click', function (e) {
        var b = e.target.closest('button'); if (!b) return;
        var k = seg.getAttribute('data-pk'), v = b.getAttribute('data-v');
        if (k === 'scheme') ctl.pad.scheme = v; else ctl.pad.inv = v === 'true';
        saveCtl(); renderControls();
      });
    });
  }

  /* ---------- local multiplayer ---------- */
  var LSLOT = ['R1', 'R2', 'R3', 'B1', 'B2', 'B3'], DEVS = ['ai', 'off', 'kb', 'pad0', 'pad1', 'pad2', 'pad3', 'pad4', 'pad5'];
  var lobby = [];
  for (var li = 0; li < 6; li++) lobby.push({ dev: li === 1 ? 'kb' : 'ai', rb: 'my' });
  try {
    var l0 = JSON.parse(localStorage.getItem('fgc.local') || 'null');
    if (Array.isArray(l0)) l0.slice(0, 6).forEach(function (s0, i) {
      if (!s0) return;
      if (/^(ai|off|kb|pad[0-5])$/.test(s0.dev)) lobby[i].dev = s0.dev;
      if (s0.rb === 'my' || (isFinite(s0.rb) && s0.rb !== null && s0.rb >= 0 && s0.rb < PRESETS.length)) lobby[i].rb = String(s0.rb);
    });
  } catch (e) { }
  var lmode = 'match'; try { if (localStorage.getItem('fgc.lmode') === 'skills') lmode = 'skills'; } catch (e) { }
  function slotOff(i) { return lmode === 'skills' && i >= 3; }
  function saveLobby() { try { localStorage.setItem('fgc.local', JSON.stringify(lobby)); } catch (e) { } }
  function padList() {
    var out = [], pads = navigator.getGamepads ? navigator.getGamepads() : [];
    for (var i = 0; i < pads.length; i++) if (pads[i] && pads[i].connected !== false) out.push(pads[i]);
    return out;
  }
  function padSigOf(list) { return list.map(function (g) { return g.index + g.id; }).join('|'); }
  function padShort(g) { return String(g.id).replace(/\s*\(.*$/, '').replace('Wireless Controller', '').trim().slice(0, 22) || 'Gamepad'; }
  function devLabel(d) {
    if (d === 'ai') return L('ИИ', 'AI'); if (d === 'off') return L('Пусто', 'Empty'); if (d === 'kb') return L('Клавиатура', 'Keyboard');
    var i = +d.slice(3), g = getPadAt(i);
    return L('Геймпад ', 'Gamepad ') + (i + 1) + (g ? ' · ' + padShort(g) : L(' (не подключён)', ' (not connected)'));
  }
  function hasHuman() { return lobby.some(function (s0, i) { return !slotOff(i) && s0.dev !== 'ai' && s0.dev !== 'off'; }); }
  function setDev(i, dev) {
    if (dev !== 'ai' && dev !== 'off') lobby.forEach(function (s0, j) { if (j !== i && s0.dev === dev) s0.dev = 'ai'; });
    lobby[i].dev = dev; saveLobby();
  }
  var padSig = '', lpPrev = {};
  function renderLocal() {
    function card(i) {
      var s0 = lobby[i], off = slotOff(i), human = !off && s0.dev !== 'ai' && s0.dev !== 'off';
      var o1 = DEVS.map(function (d) { return '<option value="' + d + '"' + (d === s0.dev ? ' selected' : '') + '>' + devLabel(d) + '</option>'; }).join('');
      var o2 = '<option value="my"' + (s0.rb === 'my' ? ' selected' : '') + '>' + L('Мой робот', 'My robot') + '</option>' +
        PRESETS.map(function (p, k) { return '<option value="' + k + '"' + (String(k) === s0.rb ? ' selected' : '') + '>' + L(p.ru, p.en) + '</option>'; }).join('');
      return '<div class="slot' + (human ? ' human' : '') + '"' + (off ? ' style="opacity:.35"' : '') + '><b>' + LSLOT[i] + '</b><select data-ls="' + i + '" data-f="dev"' + (off ? ' disabled' : '') + '>' + o1 + '</select><select data-ls="' + i + '" data-f="rb"' + (human ? '' : ' disabled') + '>' + o2 + '</select></div>';
    }
    $('local-red').innerHTML = [0, 1, 2].map(card).join('');
    $('local-blue').innerHTML = [3, 4, 5].map(card).join('');
    var pads = padList(), ok = hasHuman();
    $('local-note').textContent = L('Подключено геймпадов: ', 'Gamepads connected: ') + pads.length + L('. Нажмите кнопку на геймпаде, и он займёт свободное место (сначала R1, B1, R2, B2…). Остальные места: ИИ или пусто.', '. Press a button on a gamepad to take a free slot (R1, B1, R2, B2…). Other slots: AI or empty.');
    $('local-start').disabled = !ok; $('local-warn').hidden = ok;
    Array.prototype.forEach.call(document.querySelectorAll('#local-mode [data-lm]'), function (b) { b.classList.toggle('pri', b.getAttribute('data-lm') === lmode); });
    if (lmode === 'skills') $('local-note').textContent += L(' Skills: 2:30, три робота (R1–R3), каждый сам за себя; выигрывает тот, кто забил больше мячей. Пустые места занимает ИИ, синие отключены.', ' Skills: 2:30, three robots (R1–R3), every robot for itself; most balls scored wins. Free slots are filled by AI, blue is disabled.');
    padSig = padSigOf(pads);
  }
  function localPoll() {
    var pads = padList(), changed = false;
    pads.forEach(function (g) {
      var any = false, i;
      for (i = 0; i < g.buttons.length; i++) if (padBtn(g, i)) { any = true; break; }
      var was = lpPrev[g.index]; lpPrev[g.index] = any;
      if (!any || was) return;
      var dv = 'pad' + g.index;
      if (g.index > 5 || lobby.some(function (s0) { return s0.dev === dv; })) return;
      var order = lmode === 'skills' ? [0, 1, 2] : [0, 3, 1, 4, 2, 5], pick = -1, k;
      for (k = 0; k < order.length && pick < 0; k++) if (lobby[order[k]].dev === 'ai') pick = order[k];
      for (k = 0; k < order.length && pick < 0; k++) if (lobby[order[k]].dev === 'off') pick = order[k];
      if (pick >= 0) { setDev(pick, dv); changed = true; }
    });
    if (changed || padSigOf(pads) !== padSig) renderLocal();
  }
  function buildSlots() {
    var n = 0;
    return lobby.map(function (s0, i) {
      if (slotOff(i) || s0.dev === 'off') return { kind: 'off' };
      if (s0.dev === 'ai') return { kind: 'ai' };
      n++;
      var c = (PRESETS[+s0.rb] && s0.rb !== 'my') ? PRESETS[+s0.rb].c : cfg.robot;
      return { kind: 'human', cfg: Object.assign({}, c), code: 'P' + n, name: 'P' + n, dev: s0.dev, pid: n - 1 };
    });
  }
  function initLocal() {
    $('local-mode').addEventListener('click', function (e) {
      var b = e.target.closest ? e.target.closest('[data-lm]') : null; if (!b) return;
      lmode = b.getAttribute('data-lm') === 'skills' ? 'skills' : 'match';
      try { localStorage.setItem('fgc.lmode', lmode); } catch (er) { }
      renderLocal();
    });
    $('scr-local').addEventListener('change', function (e) {
      var t = e.target; if (!t || !t.getAttribute || t.getAttribute('data-ls') === null) return;
      var i = +t.getAttribute('data-ls'), f = t.getAttribute('data-f');
      if (f === 'dev') setDev(i, t.value); else { lobby[i].rb = t.value; saveLobby(); }
      renderLocal();
    });
  }

  /* ---------- records screen ---------- */
  function renderRecords() {
    var m = rec.match, p = rec.practice, k = rec.skills;
    var cards = [
      [m.played, L('матчей сыграно', 'matches played')], [m.wins, L('побед', 'wins')], [m.best, L('лучший счёт альянса', 'best alliance score')], [m.margin, L('лучший отрыв', 'best winning margin')],
      [p.best, L('практика: лучший счёт', 'practice: best score')], [k.best, L('Skills: больше всего мячей', 'Skills: most balls scored')], [k.wins || 0, L('Skills: побед', 'Skills: wins')]
    ];
    $('rec-grid').innerHTML = cards.map(function (c) { return '<div class="rec"><b>' + c[0] + '</b><span>' + c[1] + '</span></div>'; }).join('');
  }

  /* ---------- game state ---------- */
  var S = null, paused = false, acc = 0, last = 0, tickN = 0, resultShown = false, gmode = 'match';
  var D = null, dacc = 0;
  var keys = {}, padPrev = {}, tv = { f: 0, s: 0, eject: false, rotl: false, rotr: false };
  var cv = $('cv'), cx = cv.getContext('2d'), dcv = $('demo'), dcx = dcv.getContext('2d');

  function startGame(mode) {
    if (mode === 'local' && !hasHuman()) return;
    gmode = mode;
    var o = {
      mode: (mode === 'skills' || (mode === 'local' && lmode === 'skills')) ? 'skills' : 'match', team: cfg.team, slot: cfg.slot, cfg: Object.assign({}, cfg.robot), partners: cfg.partners,
      opponents: mode === 'match', slots: mode === 'local' ? buildSlots() : null, difficulty: cfg.diff, seed: (Math.random() * 1e9) | 0, hp: cfg.hp, code: cfg.code || 'KAZ'
    };
    S = FGC.createMatch(o); paused = false; acc = 0; resultShown = false; keys = {};
    $('pause').hidden = true; $('result').hidden = true;
    show('game'); buildBar(); resize(); beep(300, 0.05);
    $('lbl-red').textContent = S.mode === 'skills' ? L('МЯЧИ', 'BALLS') : 'RED';
    $('lbl-blue').textContent = S.mode === 'skills' ? L('ВРЕМЯ ЗАБЕГА', 'RUN TIME') : 'BLUE';
  }
  function exitGame() { S = null; show('menu'); }
  function setPause(p) { if (!S || S.phase === 'done') return; paused = p; $('pause').hidden = !p; }

  /* ---------- input ---------- */
  function kbPlayer() {
    var hs = (S && S.humans) || [];
    for (var i = 0; i < hs.length; i++) if (hs[i].human && (!hs[i].dev || hs[i].dev === 'kb')) return hs[i];
    return null;
  }
  function pressAction(a, pl) {
    if (!S || paused || S.phase === 'done') return;
    var p = pl || kbPlayer(); if (!p || !p.human) return;
    var pre = S.humans && S.humans.length > 1 ? p.pname + ': ' : '';
    if (a === 'intake') { p.intakeOn = !p.intakeOn; toast(pre + (p.intakeOn ? L('Захват включён', 'Intake on') : L('Захват выключен', 'Intake off'))); }
    else if (a === 'climb') FGC.press(S, 'climb', p);
    else if (a === 'lift') FGC.press(S, 'lift', p);
    else if (a === 'hp') { var m = ['auto', 'chute', 'ext'], i = m.indexOf(S.hp[p.team]); S.hp[p.team] = m[(i + 1) % 3]; toast(pre + L('Игрок-человек: ', 'Human player: ') + hpName(S.hp[p.team])); }
    else if (a === 'stop' && S.mode === 'skills') FGC.stopRun(S);
  }
  function hpName(m) { return m === 'auto' ? 'Auto' : m === 'chute' ? L('в лоток', 'chute') : 'Extinguisher'; }
  window.addEventListener('keydown', function (e) {
    var code = e.code;
    if (cur === 'controls' && (kbRebind || padRebind)) {
      e.preventDefault();
      if (kbRebind) {
        if (code === 'Backspace' || code === 'Delete') ctl.kb[kbRebind.a][kbRebind.i] = '';
        else if (code !== 'Escape') setKey(kbRebind.a, kbRebind.i, code);
        kbRebind = null;
      } else if (code === 'Escape' || code === 'Backspace' || code === 'Delete') {
        if (code !== 'Escape') ctl.pad.map[padRebind.a][padRebind.i] = -1;
        padRebind = null;
      } else return;
      saveCtl(); if (document.activeElement && document.activeElement.blur) document.activeElement.blur(); renderControls(); return;
    }
    if (cur !== 'game') return;
    var t = e.target; if (t && (t.tagName === 'INPUT' || t.tagName === 'SELECT')) return;
    if (['Space', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].indexOf(code) >= 0 || isBound(code)) e.preventDefault();
    if (e.repeat) { keys[code] = true; return; }
    keys[code] = true;
    if (is(code, 'pause')) { setPause(!paused); return; }
    if (is(code, 'intake')) pressAction('intake'); else if (is(code, 'climb')) pressAction('climb'); else if (is(code, 'lift')) pressAction('lift');
    else if (is(code, 'hp')) pressAction('hp'); else if (is(code, 'stop')) pressAction('stop');
  });
  window.addEventListener('keyup', function (e) { keys[e.code] = false; });
  window.addEventListener('blur', function () { keys = {}; });
  document.addEventListener('visibilitychange', function () { if (document.hidden && cur === 'game') setPause(true); });

  function getPad() {
    var pads = navigator.getGamepads ? navigator.getGamepads() : [];
    for (var i = 0; i < pads.length; i++) if (pads[i] && pads[i].connected !== false) return pads[i];
    return null;
  }
  function padBtn(g, i) { var b = g.buttons[i]; return !!b && (b.pressed || b.value > 0.4); }
  function padAny(g, list) { for (var i = 0; i < list.length; i++) if (list[i] >= 0 && padBtn(g, list[i])) return true; return false; }
  function getPadAt(i) { var pads = navigator.getGamepads ? navigator.getGamepads() : []; var g = pads[i]; return g && g.connected !== false ? g : null; }
  function padFor(p) {
    if (!p.dev) return getPad();
    if (p.dev.indexOf('pad') === 0) return getPadAt(+p.dev.slice(3));
    return null;
  }
  var padPrevBy = {};
  function padEdges() {
    var hs = S && S.humans; if (!hs) return;
    hs.forEach(function (p) {
      if (!p.human) return;
      var g = padFor(p); if (!g) return;
      PAD_ACT.forEach(function (a) {
        if (a === 'eject') return;
        var key = p.id + a, dn = padAny(g, ctl.pad.map[a]), was = padPrevBy[key]; padPrevBy[key] = dn;
        if (dn && !was) { if (a === 'pause') setPause(!paused); else pressAction(a, p); }
      });
    });
  }
  function readPad(g) {
    var o = { f: 0, t: 0, eject: false }; if (!g) return o;
    var P = ctl.pad, dz = P.dz / 100;
    function ax(i) { var v = g.axes[i] || 0, a = Math.abs(v); if (a < dz) return 0; return (v < 0 ? -1 : 1) * Math.min(1, (a - dz) / (1 - dz)); }
    var lx = ax(0), ly = ax(1), rx = ax(2), ry = ax(3), f, t;
    if (P.scheme === 'tank') { var lw = -ly, rw = -ry; f = (lw + rw) / 2; t = (lw - rw) / 2; }
    else if (P.scheme === 'single') { f = -ly; t = lx; }
    else { f = -ly; t = rx; }
    if (padBtn(g, 12)) f += 1; if (padBtn(g, 13)) f -= 1; if (padBtn(g, 15)) t += 1; if (padBtn(g, 14)) t -= 1;
    t = t * P.turn / 100; if (P.inv) t = -t;
    o.f = Math.max(-1, Math.min(1, f)); o.t = Math.max(-1, Math.min(1, t));
    o.eject = padAny(g, P.map.eject);
    return o;
  }
  function driveInput(p) {
    var useKb = !p.dev || p.dev === 'kb', pd = readPad(padFor(p));
    var f = (useKb ? held('fwd') - held('back') + tv.f : 0) + pd.f;
    var tn = (useKb ? held('right') - held('left') + (tv.rotr ? 1 : 0) - (tv.rotl ? 1 : 0) + tv.s : 0) + pd.t;
    function cl(v) { return v > 1 ? 1 : v < -1 ? -1 : v; }
    p.input.f = cl(f); p.input.s = 0; p.input.t = cl(tn);
    p.input.eject = (useKb && (held('eject') > 0 || tv.eject)) || pd.eject;
  }
  function applyInput() {
    var hs = S && S.humans; if (!hs) return;
    for (var i = 0; i < hs.length; i++) if (hs[i].human) driveInput(hs[i]);
  }
  /* touch */
  function initTouch() {
    if (window.matchMedia && matchMedia('(pointer: coarse)').matches) document.documentElement.classList.add('coarse');
    var stick = $('stick'), knob = stick.firstElementChild, id = null;
    function mv(e) {
      var r = stick.getBoundingClientRect(), dx = (e.clientX - (r.left + r.width / 2)) / 50, dy = (e.clientY - (r.top + r.height / 2)) / 50, m = Math.hypot(dx, dy);
      if (m > 1) { dx /= m; dy /= m; }
      tv.f = -dy; tv.s = dx; knob.style.transform = 'translate(' + dx * 34 + 'px,' + dy * 34 + 'px)';
    }
    stick.addEventListener('pointerdown', function (e) { id = e.pointerId; stick.setPointerCapture(id); mv(e); });
    stick.addEventListener('pointermove', function (e) { if (e.pointerId === id) mv(e); });
    function end(e) { if (e.pointerId === id) { id = null; tv.f = 0; tv.s = 0; knob.style.transform = ''; } }
    stick.addEventListener('pointerup', end); stick.addEventListener('pointercancel', end);
    Array.prototype.forEach.call($('tbtns').children, function (b) {
      var a = b.getAttribute('data-t');
      b.addEventListener('pointerdown', function (e) {
        e.preventDefault(); b.classList.add('on');
        if (a === 'eject' || a === 'rotl' || a === 'rotr') tv[a] = true;
        else if (a === 'pause') setPause(!paused); else pressAction(a);
      });
      var up = function () { b.classList.remove('on'); if (a === 'eject' || a === 'rotl' || a === 'rotr') tv[a] = false; };
      b.addEventListener('pointerup', up); b.addEventListener('pointercancel', up); b.addEventListener('pointerleave', up);
    });
  }

  /* ---------- HUD ---------- */
  var toastT = 0;
  function toast(msg) { var t = $('toast'); t.textContent = msg; t.classList.add('on'); clearTimeout(toastT); toastT = setTimeout(function () { t.classList.remove('on'); }, 1600); }
  function fmt(t) { t = Math.max(0, Math.ceil(t - 1e-9)); return Math.floor(t / 60) + ':' + ('0' + (t % 60)).slice(-2); }
  function buildBar() {
    var b = $('bar');
    b.innerHTML = '<div id="mp-bar" class="mp" hidden></div><div id="sp-bar" style="display:contents"><div class="st"><span class="ru">Бункер</span><span class="en">Hopper</span><div class="meter"><i id="m-hop"></i></div><b id="t-hop"></b></div>' +
      '<div class="st"><span class="ru">Захват</span><span class="en">Intake</span><b id="t-int"></b></div>' +
      '<div class="st"><span class="ru">Подъём</span><span class="en">Climb</span><b id="t-cl"></b></div>' +
      '<div class="st"><span class="ru">Игрок-человек</span><span class="en">Human player</span><b id="t-hp"></b></div>' +
      '<div class="st"><span class="ru">Fire Shield</span><span class="en">Fire Shield</span><b id="t-sh"></b></div>' +
      '<div class="st hint" id="t-hint"></div></div><span class="sp"></span>' +
      '<button class="btn sm" id="b-stop" type="button" hidden><span class="ru">Закончить забег</span><span class="en">End run</span></button>' +
      '<button class="btn sm" id="b-pause" type="button"><span class="ru">Пауза</span><span class="en">Pause</span></button>' +
      '<div class="keys" id="keys-hint"></div>';
    $('keys-hint').innerHTML = keyHint();
    $('b-pause').onclick = function () { setPause(true); };
    $('b-stop').onclick = function () { pressAction('stop'); };
  }
  function attachable(s, p) {
    if (p.climb.on || p.carrier || p.d.cl < 1) return false;
    var b = s.brace[p.team], t = ((p.x - b.a.x) * b.ux + (p.y - b.a.y) * b.uy) / b.L;
    if (t > 1 / 3 + 0.03 || t < -0.02) return false;
    t = Math.max(0.02, Math.min(1 / 3, t)); var q = FGC.pipePt(b, t);
    return Math.hypot(p.x - q.x, p.y - q.y) <= 46;
  }
  function mpHtml() {
    return S.humans.map(function (r) {
      var ci = FGC.climbInfo(S, r), cl = r.climb.on ? 'Z' + ci.z : r.carrier ? L('несут', 'carried') : ci.contact ? 'Contact' : '—';
      var dv = !r.dev ? '' : r.dev === 'kb' ? L('клав.', 'kbd') : 'Pad ' + (+r.dev.slice(3) + 1);
      return '<div class="pl ' + r.team + '"><b>' + r.pname + '</b><span>' + dv + '</span><div class="meter"><i style="width:' + (r.held.length / r.d.cap * 100) + '%"></i></div><b>' + r.held.length + '/' + r.d.cap + '</b><span>' + L('захват ', 'intake ') + (r.intakeOn ? 'ON' : 'OFF') + '</span><span>' + cl + '</span></div>';
    }).join('');
  }
  function updateHud() {
    if (!S) return;
    var p = S.player, R = FGC.scoreFor(S, 'red'), B = FGC.scoreFor(S, 'blue');
    if (S.mode === 'skills') {
      var bd = FGC.skillsBoard(S), lead = bd[0].goals > 0 && (!bd[1] || bd[0].goals > bd[1].goals) ? bd[0].name : '—';
      $('sc-red').textContent = p ? p.goals : 0; $('sc-blue').textContent = Math.ceil(S.sk.t) + ' s';
      $('sub-red').textContent = bd.map(function (e) { return e.name + ' ' + e.goals; }).join(' · ');
      $('sub-blue').textContent = L('лидирует: ', 'leading: ') + lead;
      $('clock').textContent = fmt(S.clock);
      $('phase').textContent = S.sk.done ? L('забег окончен', 'run over') : S.sk.started ? L('идёт забег', 'run') : L('старт с первого движения', 'starts on first move');
    } else {
      $('sc-red').textContent = R.total; $('sc-blue').textContent = B.total;
      $('sub-red').textContent = 'SU ' + R.su + ' × ' + R.mult.toFixed(2) + ' · EXT ' + R.ext + (R.partner ? ' · P ' + R.partner : '');
      $('sub-blue').textContent = 'SU ' + B.su + ' × ' + B.mult.toFixed(2) + ' · EXT ' + B.ext + (B.partner ? ' · P ' + B.partner : '');
      $('clock').textContent = fmt(S.phase === 'count' ? FGC.MATCH_T : S.clock);
      $('phase').textContent = S.phase === 'count' ? L('старт через ', 'start in ') + Math.ceil(S.cd) : S.phase === 'play' ? (S.clock <= 30 ? 'ENDGAME' : L('матч', 'match')) : S.phase === 'settle' ? L('подсчёт…', 'scoring…') : L('финал', 'final');
    }
    if (!p) return;
    var multi = !!(S.humans && S.humans.length > 1); $('sp-bar').hidden = multi; $('mp-bar').hidden = !multi;
    if (multi) { $('mp-bar').innerHTML = mpHtml(); return; }
    $('m-hop').style.width = (p.held.length / p.d.cap * 100) + '%'; $('t-hop').textContent = p.held.length + '/' + p.d.cap;
    $('t-int').textContent = p.intakeOn ? 'ON' : 'OFF';
    var ci = FGC.climbInfo(S, p);
    $('t-cl').textContent = p.climb.on ? 'Zone ' + ci.z : p.carrier ? L('несёт партнёр', 'carried') : ci.contact ? 'Contact' : '—';
    $('t-hp').textContent = hpName(S.hp[p.team]);
    $('t-sh').textContent = S.sh[p.team].q.length;
    var h = '';
    if (p.human) {
      if (p.climb.on) h = kbs('fwd') + '/' + kbs('back') + L(' вверх и вниз · ', ' up and down · ') + kbs('climb') + L(' отпустить', ' release') + (p.d.lift && !p.carrying.length ? ' · ' + kbs('lift') + L(' поднять партнёра', ' lift partner') : '');
      else if (attachable(S, p)) h = kbs('climb') + L(': взяться за трубу', ': grab the pipe');
      else if (FGC.canScoreSU(p) && p.held.length) h = kbs('eject') + L(': бросок в SU', ': score into SU');
    }
    $('t-hint').textContent = h; $('b-stop').hidden = S.mode !== 'skills';
  }

  /* ---------- results ---------- */
  function rowsMatch(R, B) {
    var rows = [
      [L('Мячи в SU', 'Balls in SU'), R.su, B.su], [L('Множитель подъёма', 'Climb multiplier'), '× ' + R.mult.toFixed(2), '× ' + B.mult.toFixed(2)],
      [L('Очки SU с множителем', 'SU points with multiplier'), R.regional, B.regional], ['Partner Climb', R.partner, B.partner],
      ['Extinguisher', R.ext, B.ext], ['Knockdown', R.knock, B.knock], ['Coopertition (' + R.z3 + ' Z3)', R.coop, B.coop]
    ];
    return rows.map(function (r) { return '<tr><td>' + r[0] + '</td><td class="n">' + r[1] + '</td><td class="n">' + r[2] + '</td></tr>'; }).join('');
  }
  function showResult() {
    resultShown = true; var html = '';
    if (S.mode === 'skills') {
      var bd = FGC.skillsBoard(S), top = bd[0].goals, tied = bd.filter(function (e) { return e.goals === top; }), me = bd.filter(function (e) { return e.mine; })[0];
      var cls = 'draw', head = L('Ничья', 'Draw');
      if (tied.length === 1) { cls = 'win'; head = (gmode === 'local' ? L('Победил ', 'Winner: ') + tied[0].name : (tied[0].mine ? L('Победа', 'Victory') : L('Победил ', 'Winner: ') + tied[0].name)); if (gmode !== 'local' && !tied[0].mine) cls = 'lose'; }
      html = '<p class="eyebrow">Skills Challenge' + (gmode === 'local' ? L(' · локальная игра', ' · local') : '') + '</p><div class="res-head ' + cls + '">' + head + '</div>' +
        '<p class="summary">' + L('Мячей в SU забито: ', 'Balls scored into SU: ') + bd.reduce(function (a, e) { return a + e.goals; }, 0) + '</p>' +
        '<table class="t">' + bd.map(function (e, i) { return '<tr><td>' + (i + 1) + '. ' + e.name + (e.mine ? L(' (ты)', ' (you)') : '') + '</td><td class="n">' + e.goals + '</td></tr>'; }).join('') + '</table>';
      if (gmode !== 'local') { rec.skills.runs++; rec.skills.best = Math.max(rec.skills.best, me ? me.goals : 0); if (tied.length === 1 && tied[0].mine) rec.skills.wins = (rec.skills.wins || 0) + 1; }
    } else {
      var R = FGC.scoreFor(S, 'red'), B = FGC.scoreFor(S, 'blue'), mine = S.player.team === 'red' ? R : B, other = S.player.team === 'red' ? B : R;
      var cls = 'draw', head = L('Ничья', 'Draw');
      if (gmode === 'local') {
        if (R.total > B.total) { cls = 'win'; head = L('Победа красных', 'Red wins'); } else if (B.total > R.total) { cls = 'win'; head = L('Победа синих', 'Blue wins'); }
      } else if (gmode === 'match') {
        if (mine.total > other.total) { cls = 'win'; head = L('Победа', 'Victory'); } else if (mine.total < other.total) { cls = 'lose'; head = L('Поражение', 'Defeat'); }
        rec.match.played++; if (cls === 'win') { rec.match.wins++; rec.match.margin = Math.max(rec.match.margin, mine.total - other.total); } rec.match.best = Math.max(rec.match.best, mine.total);
      } else { head = mine.total + L(' очков', ' pts'); rec.practice.runs++; rec.practice.best = Math.max(rec.practice.best, mine.total); }
      html = '<p class="eyebrow">' + (gmode === 'match' ? L('Матч 3×3', 'Match 3v3') : gmode === 'local' ? L('Локальная игра', 'Local game') : L('Практика', 'Practice')) + '</p><div class="res-head ' + cls + '">' + head + '</div>' +
        '<div class="scroll-x"><table class="t"><tr><th></th><th class="n" style="color:' + RED + '">RED</th><th class="n" style="color:' + BLUE + '">BLUE</th></tr>' + rowsMatch(R, B) +
        '<tr><td><b>' + L('Итого', 'Total') + '</b></td><td class="n"><b>' + R.total + '</b></td><td class="n"><b>' + B.total + '</b></td></tr></table></div>' +
        '<p class="summary">' + L('Мячи в Extinguisher, Knockdown и Coopertition общие для обоих альянсов. Множитель = 1 + сумма приростов роботов.', 'Extinguisher balls, Knockdown and Coopertition are shared by both alliances. Multiplier = 1 + sum of the robots\' increments.') + '</p>';
    }
    saveRec();
    html += '<div class="start-row"><button class="btn pri" id="r-again" type="button">' + L('Ещё раз', 'Play again') + '</button><button class="btn" id="r-cfg" type="button">' + (gmode === 'local' ? L('Лобби', 'Lobby') : L('Робот и матч', 'Robot & match')) + '</button><button class="btn" id="r-menu" type="button">' + L('В меню', 'Menu') + '</button></div>';
    $('result-card').innerHTML = html; $('result').hidden = false;
    $('r-again').onclick = function () { startGame(gmode); }; $('r-cfg').onclick = function () { S = null; show(gmode === 'local' ? 'local' : 'config'); }; $('r-menu').onclick = exitGame;
  }

  /* ---------- drawing ---------- */
  function rgba(hex, a) { var n = parseInt(hex.slice(1), 16); return 'rgba(' + (n >> 16) + ',' + ((n >> 8) & 255) + ',' + (n & 255) + ',' + a + ')'; }
  function draw(ctx, s, W, H, full) {
    ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.fillStyle = '#0f1419'; ctx.fillRect(0, 0, W, H);
    if (!s) return;
    var VX = -95, VY = -34, VW = 890, VH = 790, sc = Math.min(W / VW, H / VH), ox = (W - VW * sc) / 2 - VX * sc, oy = (H - VH * sc) / 2 - VY * sc;
    ctx.setTransform(sc, 0, 0, sc, ox, oy);
    var i, p = s.player, hum = full && p && p.human && s.phase === 'play';
    var skills = s.mode === 'skills';
    // alliance stations
    ['red', 'blue'].forEach(function (t) {
      var x0 = t === 'red' ? -90 : 700, c = t === 'red' ? RED : BLUE, mid = x0 + 45;
      if (skills && t === 'blue') c = '#6b7882';
      ctx.fillStyle = rgba(c, 0.07); ctx.fillRect(x0, 130, 90, 440);
      ctx.strokeStyle = rgba(c, 0.45); ctx.lineWidth = 1.5; ctx.setLineDash([5, 4]); ctx.strokeRect(x0, 130, 90, 440); ctx.strokeRect(x0, 575, 90, 125); ctx.setLineDash([]);
      ctx.fillStyle = rgba(c, 0.8); ctx.font = '600 11px "IBM Plex Mono", monospace'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillText('HP', mid, 640);
      ctx.save(); ctx.translate(mid, 350); ctx.rotate(t === 'red' ? -Math.PI / 2 : Math.PI / 2); ctx.fillText((t === 'red' ? 'RED' : 'BLUE') + ' ALLIANCE STATION', 0, 0); ctx.restore();
    });
    // carpet
    ctx.fillStyle = '#26312d'; ctx.fillRect(0, 0, 700, 700);
    ctx.strokeStyle = 'rgba(255,255,255,0.04)'; ctx.lineWidth = 1; ctx.beginPath();
    for (i = 60; i < 700; i += 60) { ctx.moveTo(i, 0); ctx.lineTo(i, 700); ctx.moveTo(0, i); ctx.lineTo(700, i); }
    ctx.stroke();
    // regional zones
    ctx.setLineDash([6, 5]); ctx.lineWidth = 2;
    ctx.fillStyle = rgba(RED, 0.12); ctx.strokeStyle = rgba(RED, 0.6); ctx.fillRect(0, 145, 50, 410); ctx.strokeRect(0, 145, 50, 410);
    ctx.fillStyle = rgba(BLUE, 0.12); ctx.strokeStyle = rgba(BLUE, 0.6); ctx.fillRect(650, 145, 50, 410); ctx.strokeRect(650, 145, 50, 410);
    ctx.setLineDash([]);
    // braces
    ['red', 'blue'].forEach(function (t) {
      if (skills && t === 'blue') return;
      var b = s.brace[t], c = t === 'red' ? RED : BLUE;
      ctx.lineCap = 'round';
      ctx.strokeStyle = 'rgba(0,0,0,0.38)'; ctx.lineWidth = 10; ctx.beginPath(); ctx.moveTo(b.a.x + b.nx * 9, b.a.y + b.ny * 9); ctx.lineTo(b.b.x + b.nx * 9, b.b.y + b.ny * 9); ctx.stroke();
      ctx.strokeStyle = c; ctx.lineWidth = 6; ctx.beginPath(); ctx.moveTo(b.a.x, b.a.y); ctx.lineTo(b.b.x, b.b.y); ctx.stroke();
      ctx.fillStyle = '#d7dfe4'; [b.a, b.b].forEach(function (q) { ctx.beginPath(); ctx.arc(q.x, q.y, 6, 0, 6.2832); ctx.fill(); });
      if (full && s.phase === 'play' && s.humans && s.humans.some(function (h) { return h.human && h.team === t && attachable(s, h); })) {
        var e = FGC.pipePt(b, 1 / 3); ctx.strokeStyle = '#62d391'; ctx.lineWidth = 3; ctx.setLineDash([8, 6]); ctx.beginPath(); ctx.moveTo(b.a.x, b.a.y); ctx.lineTo(e.x, e.y); ctx.stroke(); ctx.setLineDash([]);
      }
      ctx.strokeStyle = '#eef3f5'; ctx.lineWidth = 2;
      [1 / 3, 2 / 3].forEach(function (tt) { var q = FGC.pipePt(b, tt); ctx.beginPath(); ctx.moveTo(q.x - b.nx * 10, q.y - b.ny * 10); ctx.lineTo(q.x + b.nx * 10, q.y + b.ny * 10); ctx.stroke(); });
      ctx.fillStyle = 'rgba(238,243,245,0.8)'; ctx.font = '600 11px "IBM Plex Mono", monospace'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      [[1 / 6, 'Z1'], [0.5, 'Z2'], [5 / 6, 'Z3']].forEach(function (z) { var q = FGC.pipePt(b, z[0]); ctx.fillText(z[1], q.x - b.nx * 17, q.y - b.ny * 17); });
    });
    // shields
    ['red', 'blue'].forEach(function (t) {
      var sh = FGC.SH[t], c = t === 'red' ? RED : BLUE, q = s.sh[t].q.length;
      ctx.fillStyle = rgba(c, 0.2); ctx.fillRect(sh.x0, sh.y0, sh.x1 - sh.x0, sh.y1 - sh.y0);
      ctx.strokeStyle = c; ctx.lineWidth = 2; ctx.strokeRect(sh.x0, sh.y0, sh.x1 - sh.x0, sh.y1 - sh.y0);
      ctx.strokeStyle = EMBER; ctx.lineWidth = 4; ctx.beginPath(); ctx.moveTo(sh.face, sh.py0); ctx.lineTo(sh.face, sh.py1); ctx.stroke();
      ctx.fillStyle = EMBER; ctx.beginPath(); ctx.moveTo(sh.ex - 7, sh.ey + 4); ctx.lineTo(sh.ex + 7, sh.ey + 4); ctx.lineTo(sh.ex, sh.ey - 8); ctx.fill();
      ctx.fillStyle = '#eef3f5'; ctx.font = '600 14px "IBM Plex Mono", monospace'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillText(q, (sh.x0 + sh.x1) / 2 - sh.sgn * 4, 680);
      ctx.font = '500 9px "IBM Plex Mono", monospace'; ctx.fillStyle = 'rgba(238,243,245,0.6)'; ctx.fillText('FIRE SHIELD', (sh.x0 + sh.x1) / 2 - sh.sgn * 4, 640);
    });
    // SU + EXT
    ['red', 'blue'].forEach(function (t) {
      var r = FGC.SU[t], c = t === 'red' ? RED : BLUE;
      ctx.fillStyle = rgba(c, 0.18); ctx.fillRect(r.x0, r.y0, r.x1 - r.x0, r.y1 - r.y0);
      ctx.strokeStyle = c; ctx.lineWidth = 2.5; ctx.strokeRect(r.x0, r.y0, r.x1 - r.x0, r.y1 - r.y0);
      ctx.setLineDash([6, 5]); ctx.strokeStyle = rgba(c, 0.55); ctx.lineWidth = 1.5; ctx.strokeRect(r.x0, 60, r.x1 - r.x0, 40); ctx.setLineDash([]);
      var fr = Math.min(1, s.su[t] / 200), gx = t === 'red' ? r.x0 + 5 : r.x1 - 13;
      ctx.fillStyle = 'rgba(0,0,0,0.35)'; ctx.fillRect(gx, 5, 8, 50); ctx.fillStyle = EMBER; ctx.fillRect(gx, 55 - fr * 50, 8, fr * 50);
      ctx.fillStyle = '#eef3f5'; ctx.font = '700 24px Oswald, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(s.su[t], (r.x0 + r.x1) / 2, 28);
      ctx.font = '500 9px "IBM Plex Mono", monospace'; ctx.fillStyle = 'rgba(238,243,245,0.6)'; ctx.fillText('SUPPRESSION', (r.x0 + r.x1) / 2, 50);
      if (full && s.phase === 'play' && s.humans && s.humans.some(function (h) { return h.human && h.team === t && FGC.canScoreSU(h) && h.held.length; })) { ctx.strokeStyle = '#62d391'; ctx.lineWidth = 4; ctx.strokeRect(r.x0 - 3, -3, r.x1 - r.x0 + 6, 106); }
    });
    var E = FGC.EXT;
    ctx.fillStyle = 'rgba(255,138,60,0.14)'; ctx.fillRect(E.x0, E.y0, E.x1 - E.x0, E.y1 - E.y0); ctx.strokeStyle = EMBER; ctx.lineWidth = 2.5; ctx.strokeRect(E.x0, E.y0, E.x1 - E.x0, E.y1 - E.y0);
    ctx.fillStyle = '#eef3f5'; ctx.font = '700 24px Oswald, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(s.ext, 350, 28);
    ctx.font = '500 9px "IBM Plex Mono", monospace'; ctx.fillStyle = 'rgba(238,243,245,0.6)'; ctx.fillText('EXTINGUISHER', 350, 50);
    // guardrail
    ctx.strokeStyle = '#46555f'; ctx.lineWidth = 8; ctx.strokeRect(-4, -4, 708, 708);
    // balls
    var B = s.B; ctx.fillStyle = EMBER; ctx.beginPath();
    for (i = 0; i < B.n; i++) { if (B.st[i] !== 0) continue; ctx.moveTo(B.x[i] + 5, B.y[i]); ctx.arc(B.x[i], B.y[i], 5, 0, 6.2832); }
    ctx.fill(); ctx.strokeStyle = 'rgba(110,40,0,0.55)'; ctx.lineWidth = 0.8; ctx.beginPath();
    for (i = 0; i < B.n; i++) { if (B.st[i] !== 0) continue; ctx.moveTo(B.x[i] + 3, B.y[i]); ctx.arc(B.x[i], B.y[i], 3, 0, 6.2832); }
    ctx.stroke();
    // robots
    var order = s.robots.slice().sort(function (a, b) { return (a.ghost ? 1 : 0) - (b.ghost ? 1 : 0) || (a.carrier ? 1 : 0) - (b.carrier ? 1 : 0); });
    order.forEach(function (r) {
      var c = r.team === 'red' ? RED : BLUE, dark = r.team === 'red' ? '#6e2724' : '#1f3e78', act = r.intakeOn && !r.input.eject;
      ctx.save(); ctx.translate(r.x, r.y); if (r.carrier) ctx.scale(0.82, 0.82); ctx.rotate(r.th);
      ctx.fillStyle = 'rgba(0,0,0,0.3)'; ctx.fillRect(-23, -21, 50, 50);
      ctx.fillStyle = '#161c21'; ctx.fillRect(-22, -29, 16, 5); ctx.fillRect(6, -29, 16, 5); ctx.fillRect(-22, 24, 16, 5); ctx.fillRect(6, 24, 16, 5);
      ctx.fillStyle = dark; ctx.fillRect(-25, -25, 50, 50); ctx.strokeStyle = c; ctx.lineWidth = 2.5; ctx.strokeRect(-25, -25, 50, 50);
      ctx.fillStyle = act ? EMBER : '#8a949b'; var iw = r.d.iw; ctx.fillRect(21, -iw / 2, 6, iw);
      ctx.fillStyle = 'rgba(255,255,255,0.35)'; ctx.beginPath(); ctx.moveTo(-14, -9); ctx.lineTo(-5, 0); ctx.lineTo(-14, 9); ctx.lineTo(-10, 0); ctx.fill();
      ctx.restore();
      ctx.fillStyle = '#fff'; ctx.font = '600 12px "IBM Plex Mono", monospace'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(r.code, r.x, r.y);
      if (r.held.length) { ctx.fillStyle = 'rgba(0,0,0,0.5)'; ctx.fillRect(r.x - 16, r.y + 34, 32, 5); ctx.fillStyle = EMBER; ctx.fillRect(r.x - 16, r.y + 34, 32 * r.held.length / r.d.cap, 5); }
      if (r.climb.on) { ctx.fillStyle = '#62d391'; ctx.font = '700 11px "IBM Plex Mono", monospace'; ctx.fillText('Z' + FGC.zoneOf(r.climb.s), r.x, r.y - 36); }
      if (r.human && full) { ctx.strokeStyle = '#fff'; ctx.lineWidth = 2; ctx.setLineDash([5, 4]); ctx.beginPath(); ctx.arc(r.x, r.y, 38, 0, 6.2832); ctx.stroke(); ctx.setLineDash([]); ctx.fillStyle = '#fff'; ctx.font = '700 10px "IBM Plex Mono", monospace'; ctx.fillText(r.pname || L('ТЫ', 'YOU'), r.x, r.y - 45); }
    });
    // fx
    ctx.fillStyle = EMBER;
    s.fx.forEach(function (f) { var u = f.t / f.d, x = f.x + (f.tx - f.x) * u, y = f.y + (f.ty - f.y) * u - Math.sin(u * 3.1416) * 18; ctx.beginPath(); ctx.arc(x, y, 4.5, 0, 6.2832); ctx.fill(); });
    // countdown
    if (full && s.phase === 'count') {
      ctx.fillStyle = 'rgba(15,20,25,0.55)'; ctx.fillRect(0, 250, 700, 200); ctx.fillStyle = '#fff'; ctx.font = '700 120px Oswald, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(Math.ceil(s.cd), 350, 350);
    }
    if (full && skills && !s.sk.started && s.phase === 'play') {
      ctx.fillStyle = 'rgba(15,20,25,0.6)'; ctx.fillRect(100, 330, 500, 40); ctx.fillStyle = '#fff'; ctx.font = '600 16px "IBM Plex Sans", sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(L('Таймер стартует с первого движения', 'The timer starts on your first move'), 350, 350);
    }
  }

  /* ---------- sizing ---------- */
  function fit(canvas) {
    var r = canvas.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1), w = Math.max(2, Math.round(r.width * dpr)), h = Math.max(2, Math.round(r.height * dpr));
    if (canvas.width !== w || canvas.height !== h) { canvas.width = w; canvas.height = h; }
  }
  function resize() { fit(cv); fit(dcv); }
  window.addEventListener('resize', resize);
  if (window.ResizeObserver) { var ro = new ResizeObserver(resize); ro.observe($('stage')); ro.observe(dcv.parentNode); }

  /* ---------- main loop ---------- */
  function handleEvents() {
    var q = S.evq; if (!q.length) return;
    for (var i = 0; i < q.length; i++) {
      var e = q[i], now = performance.now();
      if (e === 'tick') beep(520, 0.12); else if (e === 'go') { beep(880, 0.4); toast(L('Поехали!', 'Go!')); }
      else if (e === 'score') { if (now - lastScoreBeep > 90) { beep(700, 0.05, 'triangle', 0.03); lastScoreBeep = now; } }
      else if (e === 'attach') { beep(300, 0.12, 'triangle', 0.06); toast(L('Захват трубы', 'Pipe grabbed')); }
      else if (e === 'lift') { beep(380, 0.12, 'triangle', 0.06); toast(L('Партнёр поднят', 'Partner lifted')); }
      else if (e === 'end') beep(220, 0.9, 'sawtooth', 0.06);
    }
    q.length = 0;
  }
  function newDemo() { D = FGC.createMatch({ autoplay: true, seed: (Math.random() * 1e9) | 0, difficulty: 2, hp: 'auto', slot: 1 }); dacc = 0; }
  function loop(ts) {
    requestAnimationFrame(loop);
    var dt = Math.min(0.05, (ts - last) / 1000 || 0); last = ts;
    if (cur === 'game' && S) {
      padEdges();
      if (!paused) {
        acc += dt; var n = 0;
        while (acc >= 1 / 60 && n < 4) { applyInput(); FGC.step(S, 1 / 60); acc -= 1 / 60; n++; }
        if (n === 4) acc = 0;
        handleEvents();
        if (S.phase === 'done' && !resultShown) showResult();
      }
      fit(cv); draw(cx, S, cv.width, cv.height, true);
      if ((tickN++ & 3) === 0) updateHud();
    } else if (cur === 'menu' && !document.hidden) {
      if (!D || D.phase === 'done') newDemo();
      dacc += dt; var m = 0; while (dacc >= 1 / 60 && m < 3) { FGC.step(D, 1 / 60); dacc -= 1 / 60; m++; } if (m === 3) dacc = 0;
      fit(dcv); draw(dcx, D, dcv.width, dcv.height, false);
    } else if (cur === 'local') {
      localPoll();
    } else if (cur === 'controls') {
      padPoll();
    }
  }

  /* ---------- wiring ---------- */
  document.addEventListener('click', function (e) {
    var g = e.target.closest('[data-go]'); if (g) { show(g.getAttribute('data-go')); return; }
    var m = e.target.closest('[data-mode]'); if (m) { startGame(m.getAttribute('data-mode')); }
  });
  $('home').onclick = function () { if (cur === 'game') exitGame(); else show('menu'); };
  $('lng').onclick = function () { lang = lang === 'ru' ? 'en' : 'ru'; try { localStorage.setItem('fgc.lang', lang); } catch (e) { } refreshAll(); };
  $('snd').onclick = function () { muted = !muted; try { localStorage.setItem('fgc.mute', muted ? '1' : '0'); } catch (e) { } refreshAll(); beep(600, 0.08); };
  $('b-resume').onclick = function () { setPause(false); };
  $('b-restart').onclick = function () { startGame(gmode); };
  $('b-exit').onclick = exitGame;
  $('rec-reset').onclick = function () { rec = { match: { played: 0, wins: 0, best: 0, margin: 0 }, practice: { runs: 0, best: 0 }, skills: { runs: 0, best: 0, ratio: 0 } }; saveRec(); renderRecords(); };

  initConfig(); initControls(); initLocal(); initTouch(); refreshAll(); show('menu'); requestAnimationFrame(loop);
  window.__fgc = { start: startGame, state: function () { return S; } };
})();

