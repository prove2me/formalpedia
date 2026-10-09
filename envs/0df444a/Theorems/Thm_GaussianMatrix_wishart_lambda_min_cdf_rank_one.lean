-- Prove2me | Theorems.Thm_GaussianMatrix_wishart_lambda_min_cdf_rank_one
-- name    : GaussianMatrix.wishart_lambda_min_cdf_rank_one
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:29:19.650331+00:00
-- url     : https://prove2.me/theorems/92f2aae5-ac39-40aa-b914-42b30eab36cc
-- title:
--   Case $r=1$ of Edelman's bound: $\mathbb P\{\|g\|^2\le t\}$ is the $\chi^2_k$ integral (equality)
-- statement:
--   Let $k\ge1$ and $t\ge0$. Let $g=(g_1,\dots,g_k)$ be a standard Gaussian vector, viewed as a $1\times k$ Gaussian matrix $G$, so that $\lambda_{\min}(GG^\top)=\sigma_{\min}(G^\top)^2=\|g\|_2^2$. Then
--   $$\mathbb P\big\{\lambda_{\min}(GG^\top)\le t\big\}=\int_0^t \frac{2^{(k-2)/2}\,\Gamma\!\big(\frac{k+1}{2}\big)}{\Gamma\!\big(\frac12\big)\,\Gamma(k)}\,\lambda^{(k-2)/2}e^{-\lambda/2}\,d\lambda=\int_0^t\frac{\lambda^{k/2-1}e^{-\lambda/2}}{2^{k/2}\Gamma(k/2)}\,d\lambda .$$
--   The two integrands agree by Legendre's duplication formula.
--
--   This is the $\chi^2_k$ law of $\|g\|^2$. It is exactly Edelman's density bound (`wishart_lambda_min_cdf_density_bound`) in the case $r=1$, where the bound holds with equality. It serves as a proved sanity check that the constant $c_{r,k}$ in that statement is the right one; it is not needed by the reduction of `wishart_lambda_min_tail`.
--
--   **Formalization Note.** `gaussianMatrix 1 k` is the product law on `Fin 1 → Fin k → ℝ`. The right-hand side is a `lintegral` over $(0,t]$. The constant is written exactly as the $r=1$ instance of the general constant $c_{r,k}$, after simplifying $k-1-1=k-2$ and $k-1+1=k$.
-- source:
--   standard fact: if g ~ N(0, I_k) then ‖g‖² ~ χ²_k, with density λ^{k/2−1}e^{−λ/2}/(2^{k/2}Γ(k/2)) on (0, ∞) (e.g. N. L. Johnson, S. Kotz, N. Balakrishnan, Continuous Univariate Distributions, Vol. 1, 2nd ed., Ch. 18). This is the case r = 1 of Edelman 1988, Prop. 5.1 / Tropp–Webber (B.5), where the bound is an equality.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem wishart_lambda_min_cdf_rank_one {k : ℕ} (hk : 1 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    (gaussianMatrix 1 k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      = ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
          (2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma (1 / 2) * Real.Gamma (k : ℝ))
            * x ^ (((k : ℝ) - 2) / 2) * Real.exp (-x / 2)) := by sorry

end GaussianMatrix
