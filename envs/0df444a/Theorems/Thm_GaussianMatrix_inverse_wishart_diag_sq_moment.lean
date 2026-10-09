-- Prove2me | Theorems.Thm_GaussianMatrix_inverse_wishart_diag_sq_moment
-- name    : GaussianMatrix.inverse_wishart_diag_sq_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:14:04.567383+00:00
-- url     : https://prove2.me/theorems/3418d138-2ff0-4e40-9596-245d6d7e2933
-- title:
--   Second moment of a diagonal entry of the inverse Wishart matrix: $\mathbb{E}[((GG^\top)^{-1})_{ii}^2] = 1/((k-r-1)(k-r-3))$
-- statement:
--   Let $r, k$ be natural numbers with $r + 4 \le k$, let $G \in \mathbb{R}^{r\times k}$ have independent $\mathcal{N}(0,1)$ entries, and let $W = GG^\top$ be the corresponding (real, identity-covariance) Wishart matrix with $k$ degrees of freedom. For every index $i \in \{1,\dots,r\}$ the squared diagonal entry $((W^{-1})_{ii})^2$ is integrable and
--
--   $$\mathbb{E}\Big[\big((GG^\top)^{-1}\big)_{ii}^{\,2}\Big] \;=\; \frac{1}{(k-r-1)(k-r-3)}.$$
--
--   Indeed $((GG^\top)^{-1})_{ii} = 1/\|(I-P_{-i})g_i\|^2$, where $g_i$ is the $i$-th row and $P_{-i}$ the projector onto the span of the other rows, and conditionally on those rows the squared residual is $\chi^2_{k-r+1}$; the claim is then $\mathbb{E}[(\chi^2_d)^{-2}] = 1/((d-2)(d-4))$ with $d = k-r+1$. This is the diagonal term $\alpha$ in the second-moment formulas $\mathbb{E}[(\operatorname{tr} W^{-1})^2] = r\alpha + r(r-1)\beta$ and $\mathbb{E}\|W^{-1}\|_F^2 = r\alpha + r(r-1)\gamma$.
--
--   **Formalization Note.** Lean's matrix inverse is total ($A^{-1} = 0$ for singular $A$); since $GG^\top$ is almost surely invertible this does not affect the value. The hypothesis $r+4 \le k$ is exactly the integrability threshold.
-- source:
--   standard fact (second moments of the inverse Wishart matrix): for $W \sim W_r(k, I)$, $\mathbb{E}[(W^{-1})_{ij}(W^{-1})_{kl}] = \frac{(k-r-2)\delta_{ij}\delta_{kl} + \delta_{ik}\delta_{jl} + \delta_{il}\delta_{jk}}{(k-r)(k-r-1)(k-r-3)}$; see A. K. Gupta and D. K. Nagar, Matrix Variate Distributions, Chapman & Hall/CRC 2000, Thm. 3.4.3, and D. von Rosen, Moments for the inverted Wishart distribution, Scand. J. Statist. 15 (1988) 97–109; cf. R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley 1982, Sec. 3.2 (theorem numbers from memory). This is the case $i=j=k=l$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem inverse_wishart_diag_sq_moment {r k : ℕ} (hrk : r + 4 ≤ k) (i : Fin r) :
    Integrable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂(gaussianMatrix r k)
      = 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by sorry

end GaussianMatrix
