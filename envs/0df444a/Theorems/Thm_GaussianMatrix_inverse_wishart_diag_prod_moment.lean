-- Prove2me | Theorems.Thm_GaussianMatrix_inverse_wishart_diag_prod_moment
-- name    : GaussianMatrix.inverse_wishart_diag_prod_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:16:28.373079+00:00
-- url     : https://prove2.me/theorems/69ffae3f-0983-47a5-86b3-72941665f4ac
-- title:
--   Mixed diagonal second moment of the inverse Wishart matrix: $\mathbb{E}[(W^{-1})_{ii}(W^{-1})_{jj}] = (k-r-2)/((k-r)(k-r-1)(k-r-3))$, $i\neq j$
-- statement:
--   Let $r + 4 \le k$, let $G \in \mathbb{R}^{r\times k}$ have independent $\mathcal{N}(0,1)$ entries and $W = GG^\top$. For distinct indices $i \ne j$ the product $(W^{-1})_{ii}(W^{-1})_{jj}$ is integrable and
--
--   $$\mathbb{E}\big[(W^{-1})_{ii}\,(W^{-1})_{jj}\big] \;=\; \frac{k-r-2}{(k-r)(k-r-1)(k-r-3)}.$$
--
--   This is the off-diagonal term $\beta$ in $\mathbb{E}[(\operatorname{tr} W^{-1})^2] = \sum_{i,j}\mathbb{E}[(W^{-1})_{ii}(W^{-1})_{jj}] = r\alpha + r(r-1)\beta$, i.e. in the fourth moment $\mathbb{E}\|G^\dagger\|_F^4$ of the pseudoinverse. It follows from $\alpha = \beta + 2\gamma$ (rotation identity) with $\alpha = 1/((k-r-1)(k-r-3))$ and $\gamma = 1/((k-r)(k-r-1)(k-r-3))$.
--
--   **Formalization Note.** Lean's matrix inverse returns $0$ on singular input; $GG^\top$ is a.s. invertible, so this does not affect the statement. Integrability is part of the conclusion.
-- source:
--   standard fact (second moments of the inverse Wishart matrix): for $W \sim W_r(k, I)$, $\mathbb{E}[(W^{-1})_{ij}(W^{-1})_{kl}] = \frac{(k-r-2)\delta_{ij}\delta_{kl} + \delta_{ik}\delta_{jl} + \delta_{il}\delta_{jk}}{(k-r)(k-r-1)(k-r-3)}$; A. K. Gupta and D. K. Nagar, Matrix Variate Distributions, Chapman & Hall/CRC 2000, Thm. 3.4.3; D. von Rosen, Scand. J. Statist. 15 (1988) 97–109; cf. R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley 1982, Sec. 3.2 (theorem numbers from memory). This is the case $i=j\ne k=l$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem inverse_wishart_diag_prod_moment {r k : ℕ} (hrk : r + 4 ≤ k) (i j : Fin r) (hij : i ≠ j) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j
        ∂(gaussianMatrix r k)
      = ((k : ℝ) - r - 2) / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by sorry

end GaussianMatrix
