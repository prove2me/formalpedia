-- Prove2me | Theorems.Thm_GaussianMatrix_inverse_wishart_frobenius_moment
-- name    : GaussianMatrix.inverse_wishart_frobenius_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:42:09.229197+00:00
-- url     : https://prove2.me/theorems/e7e822d8-f0a6-410e-8820-f0b7d37670ac
-- title:
--   Second Frobenius moment of an inverse-Wishart matrix: $\mathbb E\|(GG^{\mathsf T})^{-1}\|_F^2=\frac{r(k-1)}{(k-r)(k-r-1)(k-r-3)}$
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix with $r\le k-4$. Then $\|(GG^{\mathsf T})^{-1}\|_F^2$ is integrable and
--   $$\mathbb E\,\bigl\|(GG^{\mathsf T})^{-1}\bigr\|_F^2=\frac{r(k-1)}{(k-r)(k-r-1)(k-r-3)} .$$
--
--   This is the squared Frobenius norm of the inverse-Wishart matrix $W^{-1}$, $W=GG^{\mathsf T}\sim\mathrm{Wishart}_r(k,I)$; it is the companion of the nuclear-norm second moment and follows from the second-order moments $\mathbb E[(W^{-1})_{ij}(W^{-1})_{kl}]$ of the inverse-Wishart distribution. Since $\|(GG^{\mathsf T})^{-1}\|_F^2=\|G^{\dagger}(G^{\dagger})^{\mathsf T}\|_F^2$, it controls the fourth moments of the singular values of $G^{\dagger}$.
--
--   **Formalization Note.** Mathlib's inverse is total ($0$ on the singular null set), which does not affect the integral; the conclusion is the conjunction of integrability and the identity.
-- source:
--   J. A. Tropp, R. J. Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis, and applications*, 2023, https://arxiv.org/abs/2306.12418 (v1), Appendix B p. 51, Lemma B.2 (Inverse moment bounds), third formula: $\mathbb E\|(GG^*)^{-1}\|_F^2=\frac{r(k-1)}{(k-r)(k-r-1)(k-r-3)}$ for $r\le k-4$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem inverse_wishart_frobenius_moment {r k : ℕ} (hrk : r + 4 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)
      (gaussianMatrix r k) ∧
    ∫ G, frobSq (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ∂(gaussianMatrix r k)
      = (r : ℝ) * ((k : ℝ) - 1)
          / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by sorry
end GaussianMatrix
