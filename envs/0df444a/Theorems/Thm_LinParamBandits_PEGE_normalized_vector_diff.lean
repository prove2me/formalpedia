-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_normalized_vector_diff
-- name    : LinParamBandits.PEGE.normalized_vector_diff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:29.756977+00:00
-- url     : https://prove2.me/theorems/b87f1656-fbad-409a-a3e6-1a56e4966fbe
-- title:
--   Lemma 3.5 — ‖w/‖w‖ − z/‖z‖‖ ≤ 2‖w − z‖/max{‖z‖, ‖w‖}
-- statement:
--   Let $z, w \in \mathbb R^r$, not both equal to zero, and let $e$ be a fixed unit vector, used as the value of $0/\|0\|$. Then
--   $$\left\| \frac{w}{\|w\|} - \frac{z}{\|z\|} \right\| \le \frac{2\|w - z\|}{\max\{\|z\|, \|w\|\}}.$$
--
--   This deterministic inequality turns the estimation error $\|\widehat Z(c) - z\|$ into an error in the direction of the estimate, which is what the SBAR condition controls.
--
--   **Formalization Note** $w/\|w\|$ is `normalize e w`, equal to $e$ at $w = 0$ and to $\|w\|^{-1} w$ otherwise; the statement holds for every unit vector $e$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma 3.5, p. 17

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Lemma 3.5 (Difference Between Normalized Vectors), Rusmevichientong, Tsitsiklis,
arXiv:0812.3465v2, p. 17: for any `z, w ∈ ℝ^r`, not both zero,
`‖w/‖w‖ − z/‖z‖‖ ≤ 2 ‖w − z‖ / max{‖z‖, ‖w‖}`, where `0/‖0‖` is a fixed unit vector `e`. -/
theorem normalized_vector_diff {r : ℕ} (e : LinParamBandits.LowerBound.Vec r) (he : ‖e‖ = 1) (z w : LinParamBandits.LowerBound.Vec r)
    (hzw : ¬(z = 0 ∧ w = 0)) :
    ‖normalize e w - normalize e z‖ ≤ 2 * ‖w - z‖ / max ‖z‖ ‖w‖ := by sorry
end LinParamBandits.PEGE
