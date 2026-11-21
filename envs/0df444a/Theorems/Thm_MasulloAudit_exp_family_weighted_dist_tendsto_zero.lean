-- Prove2me | Theorems.Thm_MasulloAudit_exp_family_weighted_dist_tendsto_zero
-- name    : MasulloAudit.exp_family_weighted_dist_tendsto_zero
-- status  : Proved
-- author  : @lll
-- created : 2026-11-21T00:32:17.924029+00:00
-- url     : https://prove2.me/theorems/c979640a-586d-43ae-94c4-2d870d08fd96
-- title:
--   The exponential family $s\mapsto e^{isu}$ is continuous in weighted $L^2$
-- statement:
--   Let $w:\mathbf R\to\mathbf R$ be integrable with $w\ge0$, and let $t\in\mathbf R$. Then
--
--   $$
--   \int_{\mathbf R}\bigl|e^{itu}-e^{isu}\bigr|^2\,w(u)\,du\longrightarrow0\qquad(s\to t).
--   $$
--
--   So the exponential family $s\mapsto e^{isu}$ is continuous in $L^2(\mathbf R,w\,du)$. Since $|e^{itu}-e^{isu}|=|1-e^{i(s-t)u}|$, the distance depends only on $s-t$, so the continuity is uniform in $t$. In logarithmic coordinates the dual basis vectors of Masullo's draft (Prop. 10.2.2.2, pp. 446–447, case $m=0$) are of this form, with an integrable weight given by the dual Hardy–Sobolev norm. Combined with `MasulloAudit.biorthogonal_norm_tendsto_top_of_continuous`, this shows that biorthogonal functionals attached to zeros with nearby ordinates have norms tending to infinity.
--
--   **Formalization Note.** $|e^{itu}-e^{isu}|^2$ is the squared complex norm, and the integral is a Bochner integral.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf; Terminology 10.2.1.2(2) (p. 444), proof of Thm 10.3.1.1 (p. 451), (10.4.2.24) (p. 463), Prop. 10.2.2.2 (pp. 446-447)

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic

open Filter Topology MeasureTheory

namespace MasulloAudit

/-- For an integrable nonnegative weight `w`, the weighted squared distance
`∫ ‖e^{itu} - e^{isu}‖² w(u) du` tends to `0` as `s → t`. -/
theorem exp_family_weighted_dist_tendsto_zero (w : ℝ → ℝ) (hw : Integrable w)
    (hw0 : ∀ u, 0 ≤ w u) (t : ℝ) :
    Tendsto (fun s : ℝ => ∫ u : ℝ,
        ‖Complex.exp (Complex.I * t * u) - Complex.exp (Complex.I * s * u)‖ ^ 2 * w u)
      (𝓝 t) (𝓝 0) := by sorry

end MasulloAudit
