-- Prove2me | Theorems.Thm_GaussianMatrix_inverse_wishart_mean
-- name    : GaussianMatrix.inverse_wishart_mean
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:38:35.32302+00:00
-- url     : https://prove2.me/theorems/8a522b07-3d3d-4dfc-a4db-1813112fae4c
-- title:
--   Inverse-Wishart mean: $\mathbb E\,(GG^{\mathsf T})^{-1}=\frac{1}{k-r-1}I_r$ for a Gaussian $G\in\mathbb R^{r\times k}$, $r\le k-2$
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix with $r\le k-2$. Then every entry of $(GG^{\mathsf T})^{-1}$ is integrable and
--   $$\mathbb E\,(GG^{\mathsf T})^{-1}=\frac{1}{k-r-1}\,I_r .$$
--
--   The matrix $W=GG^{\mathsf T}$ is Wishart distributed with $k$ degrees of freedom and identity scale, and $W^{-1}$ is inverse-Wishart; this is the classical formula for its mean. Taking the trace gives $\mathbb E\|G^{\dagger}\|_F^2=\mathbb E\operatorname{tr}(GG^{\mathsf T})^{-1}=r/(k-r-1)$, the quantity governing the expected Frobenius error of the randomized SVD.
--
--   **Formalization Note.** The statement is entrywise: for all $i,j$, the function $G\mapsto((GG^{\mathsf T})^{-1})_{ij}$ is integrable under $\gamma_{r,k}$ and its integral equals $(k-r-1)^{-1}(I_r)_{ij}$. Mathlib's inverse is total ($0$ on the singular null set), which does not affect the integral.
-- source:
--   J. A. Tropp, R. J. Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis, and applications*, 2023, https://arxiv.org/abs/2306.12418 (v1), Appendix B p. 51, Lemma B.2 (Inverse moment bounds), first formula: $\mathbb E(GG^*)^{-1}=\frac{1}{k-r-1}I$ for $r\le k-2$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem inverse_wishart_mean {r k : ℕ} (hrk : r + 2 ≤ k) :
    (∀ i j : Fin r, Integrable (fun G : Fin r → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) (gaussianMatrix r k)) ∧
    ∀ i j : Fin r, ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k)
      = (1 / ((k : ℝ) - r - 1)) * (1 : Matrix (Fin r) (Fin r) ℝ) i j := by sorry
end GaussianMatrix
