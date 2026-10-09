-- Prove2me | Theorems.Thm_GaussianMatrix_wishart_lambda_min_cdf_density_bound
-- name    : GaussianMatrix.wishart_lambda_min_cdf_density_bound
-- status  : Open
-- author  : @tc
-- created : 2026-10-09T08:27:23.911469+00:00
-- url     : https://prove2.me/theorems/86a4ed0c-832c-4bb5-a8d7-efc12b3a4f57
-- title:
--   Edelman's density bound for $\lambda_{\min}$ of a Wishart matrix, integrated: $\mathbb P\{\lambda_{\min}(GG^\top)\le t\}\le\int_0^t c_{r,k}\lambda^{(k-r-1)/2}e^{-\lambda/2}d\lambda$
-- statement:
--   Let $1\le r\le k$ be integers and let $G$ be an $r\times k$ random matrix with independent standard normal entries, so that $W=GG^\top$ is a real Wishart matrix $W_r(k,I)$. Write
--   $$\lambda_{\min}(GG^\top)=\sigma_{\min}(G^\top)^2,\qquad \sigma_{\min}(G^\top)=\inf_{x\in\mathbb R^r,\ \|x\|_2=1}\|G^\top x\|_2 ,$$
--   and put
--   $$c_{r,k}=\frac{2^{(k-r-1)/2}\,\Gamma\!\big(\frac{k+1}{2}\big)}{\Gamma\!\big(\frac r2\big)\,\Gamma(k-r+1)}.$$
--   Then for every $t>0$,
--   $$\mathbb P\big\{\lambda_{\min}(GG^\top)\le t\big\}\;\le\;\int_0^t c_{r,k}\,\lambda^{(k-r-1)/2}e^{-\lambda/2}\,d\lambda .$$
--
--   This is the integrated form of Edelman's pointwise density bound $f_{\lambda_{\min}}(\lambda)\le c_{r,k}\lambda^{(k-r-1)/2}e^{-\lambda/2}$ for $\lambda>0$ (Tropp–Webber eq. (B.5)). Edelman's derivation starts from the joint eigenvalue density of $W$, $\propto\prod_i\lambda_i^{(k-r-1)/2}e^{-\lambda_i/2}\prod_{i<j}|\lambda_i-\lambda_j|$. It writes $f_{\lambda_{\min}}(\lambda)=\lambda^{(k-r-1)/2}e^{-\lambda/2}\,h(\lambda)$, where $h$ is nonincreasing, and bounds $h(\lambda)\le h(0^+)=c_{r,k}$. The bound is therefore sharp as $\lambda\to0^+$, and for $r=1$ it is an equality: $c_{1,k}\lambda^{k/2-1}e^{-\lambda/2}$ is exactly the $\chi^2_k$ density. Combined with `tw_gamma_ratio_bound` and `integral_power_exp_le`, it gives the lower-tail bound `wishart_lambda_min_tail` (TW (B.7)). That bound in turn gives the tail and moment bounds for $\|G^\dagger\|$ and $\|(GG^\top)^{-1}\|$.
--
--   **Formalization Note.** The law of $G$ is `gaussianMatrix r k` on `Fin r → Fin k → ℝ`, and $\lambda_{\min}(GG^\top)$ is written `sMin (Matrix.of G)ᵀ ^ 2`, so no eigenvalues need to be defined. The right-hand side is a lower Lebesgue integral (`lintegral`) over $(0,t]$ of `ENNReal.ofReal` of the density bound. The integrand is integrable, since $(k-r-1)/2\ge-\tfrac12>-1$, and the `lintegral` form avoids Bochner-integral junk values. $\Gamma$ is `Real.Gamma`, and the powers are real powers, positive on $(0,t]$. The hypothesis $r\ge1$ is necessary: for $r=0$, `Real.Gamma 0 = 0` makes $c_{0,k}=0$, while the event is the whole space. Only the interval form is stated, because it is all that (B.7) needs; it is weaker than the pointwise density bound.
-- source:
--   A. Edelman, Eigenvalues and condition numbers of random matrices, SIAM J. Matrix Anal. Appl. 9(4) (1988) 543–560, Prop. 5.1 (density bound for λ_min of a real Wishart matrix; the proposition number is the one cited by Tropp–Webber and was not checked against the original); restated in J. A. Tropp and R. J. Webber, Randomized algorithms for low-rank matrix approximation: design, analysis, and applications, arXiv:2306.12418, Appendix B, proof of Lemma B.3, eq. (B.5) (after Legendre duplication of Edelman's constant). The statement here is the integral of (B.5) over (0, t].

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem wishart_lambda_min_cdf_density_bound {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (t : ℝ)
    (ht : 0 < t) :
    (gaussianMatrix r k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
          (2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
            * x ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-x / 2)) := by sorry

end GaussianMatrix
