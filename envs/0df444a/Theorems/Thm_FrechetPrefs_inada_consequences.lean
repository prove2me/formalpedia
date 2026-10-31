-- Prove2me | Theorems.Thm_FrechetPrefs_inada_consequences
-- name    : FrechetPrefs.inada_consequences
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:56.744723+00:00
-- url     : https://prove2.me/theorems/4a07ce0d-3d15-426b-a4a1-1b69bbc66536
-- title:
--   pp.ec6–ec7 — consequences of Assumption 1: $u''\le 0$, $u'$ decreasing, $u'\ge 0$, integrability
-- statement:
--   Let $u$ satisfy Assumption 1. Then on $(0,\infty)$:
--
--   1. $u''\le0$;
--   2. $u'$ is decreasing;
--   3. $u'\ge0$;
--   4. for $0<K\le x$, $|u(x)|\le|u(K)|+u'(K)(x-K)$;
--   5. $u$ is integrable for every measure of the floor class at $K>0$.
--
--   The first three are used without comment on pp.ec6–ec7, where the proof writes "since $u''\le0$" and "$u'$ is a decreasing function". The last two make the expected utility in (4) well defined on the floor class.
--
--   Differences from the source: none.
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), (EC.7), p.ec6, and p.ec7

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- Consequences of Assumption 1 used on pp.ec6–ec7 of manuscript MS-DEC-19-01009-REV: `u″ ≤ 0`, `u′`
is decreasing and `u′ ≥ 0` on `(0,∞)`. For a floor `K > 0`, `u` grows at most linearly on
`[K,∞)` and hence is integrable for every measure of the floor class, so that the expected utility in
(4) is not a junk value. -/
theorem inada_consequences (u : ℝ → ℝ) (hu : IsInadaUtility u) :
    (∀ x, 0 < x → deriv (deriv u) x ≤ 0) ∧
    AntitoneOn (deriv u) (Ioi 0) ∧
    (∀ x, 0 < x → 0 ≤ deriv u x) ∧
    (∀ K x, 0 < K → K ≤ x → |u x| ≤ |u K| + deriv u K * (x - K)) ∧
    (∀ K, 0 < K → ∀ μ ∈ floorClass K, Integrable u (μ : Measure ℝ)) := by sorry

end FrechetPrefs
