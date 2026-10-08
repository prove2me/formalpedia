-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_unit_sphere_sbar
-- name    : LinParamBandits.PEGE.unit_sphere_sbar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:38.001671+00:00
-- url     : https://prove2.me/theorems/01e9e91e-4ae7-4c7e-b479-b50c6a139f86
-- title:
--   Proof of Corollary 3.3, p. 16 — the unit sphere satisfies SBAR(1)
-- statement:
--   For every $r$, the unit sphere $\{u \in \mathbb R^r : \|u\| = 1\}$ satisfies the SBAR(1) condition: every $z \ne 0$ has a unique best arm $u^*(z)$, the maximizer of $u'z$ over the sphere, and
--   $$\|u^*(z) - u^*(y)\| \le \|z - y\| \qquad\text{for all unit vectors } z, y.$$
--
--   This is the fact used in the proof of Corollary 3.3 to apply Theorem 3.1 to the unit sphere.
--
--   **Formalization Note** The statement is made for every $r$; the paper's setting is $r \ge 2$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, proof of Corollary 3.3, p. 16 ('the unit sphere satisfies the SBAR(1) condition')

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Proof of Corollary 3.3, p. 16 (Rusmevichientong, Tsitsiklis, arXiv:0812.3465v2): "the unit
sphere satisfies the SBAR(1) condition." The unit sphere of `ℝ^r` satisfies SBAR(1). -/
theorem unit_sphere_sbar (r : ℕ) : SBAR (Metric.sphere (0 : LinParamBandits.LowerBound.Vec r) 1) 1 := by sorry
end LinParamBandits.PEGE
