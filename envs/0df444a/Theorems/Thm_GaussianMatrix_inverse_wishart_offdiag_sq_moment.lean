-- Prove2me | Theorems.Thm_GaussianMatrix_inverse_wishart_offdiag_sq_moment
-- name    : GaussianMatrix.inverse_wishart_offdiag_sq_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:17:09.637291+00:00
-- url     : https://prove2.me/theorems/d89539b0-534c-4c88-b9b1-b7033d14c50c
-- title:
--   Second moment of an off-diagonal entry of the inverse Wishart matrix: $\mathbb{E}[(W^{-1})_{ij}^2] = 1/((k-r)(k-r-1)(k-r-3))$, $i\neq j$
-- statement:
--   Let $r + 4 \le k$, let $G \in \mathbb{R}^{r\times k}$ have independent $\mathcal{N}(0,1)$ entries and $W = GG^\top$. For distinct indices $i \ne j$ the squared entry $(W^{-1})_{ij}^2$ is integrable and
--
--   $$\mathbb{E}\big[(W^{-1})_{ij}^2\big] \;=\; \frac{1}{(k-r)(k-r-1)(k-r-3)}.$$
--
--   Writing $H$ for the matrix of the rows other than $g_i$, $c = (HH^\top)^{-1}Hg_i$ for the regression coefficients of $g_i$ on those rows and $Q = \|(I-P_H)g_i\|^2$ for the squared residual, one has $(W^{-1})_{ij} = -c_{j'}/Q$ (with $j'$ the position of row $j$ in $H$). Conditionally on $H$, $c$ and $Q$ are independent, $\mathbb{E}[c_{j'}^2 \mid H] = ((HH^\top)^{-1})_{j'j'}$ and $Q\sim\chi^2_{k-r+1}$, so the claim follows from $\mathbb{E}[((HH^\top)^{-1})_{j'j'}] = 1/(k-r)$ and $\mathbb{E}[Q^{-2}] = 1/((k-r-1)(k-r-3))$. This is the term $\gamma$ in $\mathbb{E}\|W^{-1}\|_F^2 = r\alpha + r(r-1)\gamma$.
--
--   **Formalization Note.** Lean's matrix inverse returns $0$ on singular input; $GG^\top$ is a.s. invertible. Integrability is part of the conclusion.
-- source:
--   standard fact (second moments of the inverse Wishart matrix): for $W \sim W_r(k, I)$, $\mathbb{E}[(W^{-1})_{ij}(W^{-1})_{kl}] = \frac{(k-r-2)\delta_{ij}\delta_{kl} + \delta_{ik}\delta_{jl} + \delta_{il}\delta_{jk}}{(k-r)(k-r-1)(k-r-3)}$; A. K. Gupta and D. K. Nagar, Matrix Variate Distributions, Chapman & Hall/CRC 2000, Thm. 3.4.3; D. von Rosen, Scand. J. Statist. 15 (1988) 97–109; cf. R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley 1982, Sec. 3.2 (theorem numbers from memory). This is the case $i=k\ne j=l$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem inverse_wishart_offdiag_sq_moment {r k : ℕ} (hrk : r + 4 ≤ k) (i j : Fin r) (hij : i ≠ j) :
    Integrable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2 ∂(gaussianMatrix r k)
      = 1 / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by sorry

end GaussianMatrix
