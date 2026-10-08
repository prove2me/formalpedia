-- Prove2me | Theorems.Thm_LindleyQueue_Stability_case_ii
-- name    : LindleyQueue.Stability.case_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:36:42.942466+00:00
-- url     : https://prove2.me/theorems/b94e5dd8-f62a-4329-83c3-adea9fd0a0b7
-- title:
--   Case (ii) — if $\mathscr{E}(u) < 0$ then $\lim_{x\to\infty} F(x) = 1$
-- statement:
--   In Lindley's single-server queue (Assumptions 1–2), let $u = s - t$ and let $F(x) = p(U_s \le x \text{ for all } s \ge 1)$ for $x \ge 0$, $F(x) = 0$ for $x < 0$, be the limit of the waiting-time distribution functions. If $\mathscr{E}(u) < 0$, then
--
--   $$
--   \lim_{x \to \infty} F(x) = 1.
--   $$
--
--   Since $F$ is nondecreasing, right-continuous on $[0,\infty)$ and vanishes on $(-\infty, 0)$, this says that $F$ is a proper distribution function: when the mean service time is smaller than the mean interarrival time, an equilibrium waiting-time distribution exists.
--
--   **Formalization Note** $\mathscr{E}(u)$ is the Bochner integral of `u 0`, integrable by Assumptions 1–2.
-- source:
--   Lindley (Proc. Camb. Phil. Soc. 48, 1952), §4, case (ii), p. 280

import Mathlib
import Definitions.Def_LindleyQueue_Stability_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace LindleyQueue.Stability

/-- Case (ii), p. 280: if `𝓔(u) < 0` then `F(x) → 1` as `x → ∞`. -/
theorem case_ii {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Input Ω P) (hneg : ∫ ω, Q.u 0 ω ∂P < 0) :
    Tendsto Q.Flim atTop (𝓝 1) := by sorry

end LindleyQueue.Stability
