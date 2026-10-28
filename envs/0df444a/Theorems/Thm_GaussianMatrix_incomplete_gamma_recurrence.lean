-- Prove2me | Theorems.Thm_GaussianMatrix_incomplete_gamma_recurrence
-- name    : GaussianMatrix.incomplete_gamma_recurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:32:49.353195+00:00
-- url     : https://prove2.me/theorems/1856f72b-0d62-4ba5-842f-14a6afa432c6
-- title:
--   Incomplete-gamma recurrence for the $e^{-t/2}$ scaling
-- statement:
--   Let $a>-1$ and $x\ge0$.  Then
--   $$\int_x^{\infty} t^{a+1}e^{-t/2}\,dt
--   =2x^{a+1}e^{-x/2}+2(a+1)\int_x^{\infty}t^{a}e^{-t/2}\,dt .$$
--
--   **Proof.**  Integrate by parts on $[x,\infty)$ with $u=t^{a+1}$ and
--   $dv=e^{-t/2}\,dt$, so $v=-2e^{-t/2}$:
--   $$\int_x^{\infty}t^{a+1}e^{-t/2}\,dt
--   =\Big[-2t^{a+1}e^{-t/2}\Big]_{x}^{\infty}+2(a+1)\int_x^{\infty}t^{a}e^{-t/2}\,dt .$$
--   The term at $+\infty$ vanishes because $t^{a+1}e^{-t/2}\to0$, and the
--   term at $x$ contributes $2x^{a+1}e^{-x/2}$.  $\square$
--
--   **Why this matters.**  This is the incomplete-gamma recurrence for the
--   $e^{-t/2}$ scaling.  It is the only non-elementary ingredient of the
--   $r=2$ real-Wishart Selberg integral
--   $$\int_{0<l_1<l_2}(l_1l_2)^a e^{-(l_1+l_2)/2}(l_2-l_1)\,dl_1\,dl_2
--   =4(k-2)!\qquad\bigl(a=\tfrac{k-3}{2}\bigr),$$
--   which is the normalisation of the joint density of the ordered eigenvalues
--   of a real Wishart matrix, and hence the input to Edelman's bound
--   $\mathbb P\{\lambda_{\min}\le t\}\le\int_0^t c_{r,k}\lambda^{(k-r-1)/2}
--   e^{-\lambda/2}\,d\lambda$ (the open theorem
--   `wishart_lambda_min_cdf_density_bound`, `86a4ed0c`).
--
--   Mathlib provides the complete gamma integral
--   `integral_rpow_mul_exp_neg_mul_rpow` and the complete recurrence
--   `Real.Gamma_add_one`, but no incomplete gamma function; this statement
--   supplies the incomplete analogue directly, so that the Selberg integral
--   can be evaluated without new Mathlib infrastructure.
--
--   **Formalisation note.**  The integrals are lower Lebesgue integrals over
--   `Set.Ioi x` of the nonnegative function `t ^ a * exp (-t/2)`; the
--   hypothesis `-1 < a` is what makes them finite.
-- source:
--   Gaussian Random Matrices II mission 1dfc2230-f260-4532-b3f9-7d60b9f4b139; supports the published child d094b839-a36e-46d9-b53f-869315181b30 wishart_lambda_min_law_le (real-Wishart eigenvalue density), which in turn unblocks 86a4ed0c-832c-4bb5-a8d7-efc12b3a4f57 wishart_lambda_min_cdf_density_bound

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- The incomplete-gamma recurrence for the `exp (-t/2)` scaling.

For `-1 < a` and `0 <= x`, integration by parts on `[x, ∞)` with
`u = t^(a+1)` and `dv = exp (-t/2) dt` (so `v = -2 exp (-t/2)`) gives

$$
\int_x^{\infty} t^{a+1} e^{-t/2}\,dt
= 2 x^{a+1} e^{-x/2} + 2(a+1)\int_x^{\infty} t^{a} e^{-t/2}\,dt ,
$$

the boundary term at `+∞` vanishing because `t^{a+1} e^{-t/2} -> 0`.

This is the only non-elementary ingredient of the `r = 2` real-Wishart
Selberg integral, whose value is `4 (k-2)!`; Mathlib provides the
*complete* gamma integral `integral_rpow_mul_exp_neg_mul_rpow` and the
recurrence `Real.Gamma_add_one`, but no incomplete gamma function.  The
present statement supplies the incomplete analogue directly as an integral.

**Formalisation note.**  The integrals are lower Lebesgue integrals over
`Set.Ioi x` of the nonnegative function `t ^ a * exp (-t/2)`; the
hypothesis `-1 < a` is what makes them finite. -/
theorem incomplete_gamma_recurrence {a x : ℝ} (ha : -1 < a) (hx : 0 ≤ x) :
    (∫ t in Set.Ioi x, t ^ (a + 1) * Real.exp (-t / 2))
      = 2 * x ^ (a + 1) * Real.exp (-x / 2)
        + 2 * (a + 1) * (∫ t in Set.Ioi x, t ^ a * Real.exp (-t / 2)) := by
  sorry

end GaussianMatrix
