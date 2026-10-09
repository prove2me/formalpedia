-- Prove2me | Theorems.Thm_GaussianMatrix_inv_sq_chi_square_moment
-- name    : GaussianMatrix.inv_sq_chi_square_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:13:24.801125+00:00
-- url     : https://prove2.me/theorems/0fe674e1-53a3-4338-a151-09bc514f0d28
-- title:
--   Inverse second moment of the chi-square distribution: $\mathbb{E}[(\chi^2_d)^{-2}] = 1/((d-2)(d-4))$ for $d \ge 5$
-- statement:
--   Let $d \ge 5$ and let $x = (x_1,\dots,x_d)$ have independent standard normal coordinates, so that $\Xi = \sum_{j=1}^d x_j^2$ has the chi-square distribution with $d$ degrees of freedom. Then $\Xi^{-2}$ is integrable and
--
--   $$\mathbb{E}\big[\Xi^{-2}\big] \;=\; \int_{\mathbb{R}^d} \Big(\sum_{j=1}^d x_j^2\Big)^{-2} d\gamma_d(x) \;=\; \frac{\Gamma(d/2-2)}{4\,\Gamma(d/2)} \;=\; \frac{1}{(d-2)(d-4)},$$
--
--   where $\gamma_d$ is the standard Gaussian measure on $\mathbb{R}^d$.
--
--   This is the second inverse moment of the chi-square law. Applied with $d = k-r+1$ degrees of freedom it yields $\mathbb{E}\big[((GG^\top)^{-1})_{ii}^2\big] = 1/((k-r-1)(k-r-3))$ for an $r\times k$ standard Gaussian matrix $G$, the diagonal ingredient of the second moments of the inverse Wishart matrix.
--
--   **Formalization Note.** The integrand is written `((∑ j, x j ^ 2)⁻¹) ^ 2`; with Lean's convention $0^{-1} = 0$ it is defined everywhere (the event $\Xi = 0$ is null). The hypothesis $d \ge 5$ is sharp: for $d \le 4$ the integral diverges.
-- source:
--   standard fact: for $\Xi \sim \chi^2_d$ and $s < d/2$, $\mathbb{E}[\Xi^{-s}] = \Gamma(d/2 - s)/(2^s\,\Gamma(d/2))$; see N. L. Johnson, S. Kotz, N. Balakrishnan, Continuous Univariate Distributions, Vol. 1, 2nd ed., Wiley 1994, Ch. 18 (moments of the chi-square distribution) [chapter cited from memory]; the case $s=1$ is Halko–Martinsson–Tropp, SIAM Review 53(2), 2011, Appendix A.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem inv_sq_chi_square_moment {d : ℕ} (hd : 5 ≤ d) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ 2)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = 1 / (((d : ℝ) - 2) * ((d : ℝ) - 4)) := by sorry

end GaussianMatrix
