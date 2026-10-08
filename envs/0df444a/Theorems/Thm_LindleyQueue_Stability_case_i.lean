-- Prove2me | Theorems.Thm_LindleyQueue_Stability_case_i
-- name    : LindleyQueue.Stability.case_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:34:27.102648+00:00
-- url     : https://prove2.me/theorems/111509df-6b46-4b96-8ee7-f45f419e7cc5
-- title:
--   Case (i) — if $\mathscr{E}(u) > 0$ then $F(x) = 0$ for all $x$
-- statement:
--   In Lindley's single-server queue (Assumptions 1–2), let $u = s - t$ and let $F(x) = p(U_s \le x \text{ for all } s \ge 1)$ for $x \ge 0$, $F(x) = 0$ for $x < 0$, be the limit of the waiting-time distribution functions. If
--
--   $$
--   \mathscr{E}(u) > 0,
--   $$
--
--   then $F(x) = 0$ for every real $x$.
--
--   In words: when the mean service time exceeds the mean interarrival time, the waiting-time distribution does not tend to a limiting distribution; the waiting time grows and a large queue builds up.
--
--   **Formalization Note** $\mathscr{E}(u)$ is the Bochner integral of `u 0`, which is integrable by Assumptions 1–2 (all $u_r$ have the same law).
-- source:
--   Lindley (Proc. Camb. Phil. Soc. 48, 1952), §4, case (i), p. 280

import Mathlib
import Definitions.Def_LindleyQueue_Stability_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace LindleyQueue.Stability

/-- Case (i), p. 280: if `𝓔(u) > 0` then `F(x) = 0` for all `x`. -/
theorem case_i {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Input Ω P) (hpos : 0 < ∫ ω, Q.u 0 ω ∂P) (x : ℝ) :
    Q.Flim x = 0 := by sorry

end LindleyQueue.Stability
