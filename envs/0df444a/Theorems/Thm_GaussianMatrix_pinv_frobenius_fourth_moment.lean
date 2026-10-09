-- Prove2me | Theorems.Thm_GaussianMatrix_pinv_frobenius_fourth_moment
-- name    : GaussianMatrix.pinv_frobenius_fourth_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:39:53.141131+00:00
-- url     : https://prove2.me/theorems/75c872a4-bde7-4417-9703-0c6fb8b7a261
-- title:
--   Fourth Frobenius moment of a pseudo-inverted Gaussian matrix: $\mathbb E\|G^{\dagger}\|_F^4=\frac{r^2(k-r)-2r(r-1)}{(k-r)(k-r-1)(k-r-3)}$
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix with $r\le k-4$ and $G^{\dagger}=G^{\mathsf T}(GG^{\mathsf T})^{-1}$. Then $\|G^{\dagger}\|_F^4$ is integrable and
--   $$\mathbb E\,\|G^{\dagger}\|_F^4=\mathbb E\bigl[\operatorname{tr}(GG^{\mathsf T})^{-1}\bigr]^2=\frac{r^2(k-r)-2r(r-1)}{(k-r)(k-r-1)(k-r-3)} .$$
--
--   Since $(GG^{\mathsf T})^{-1}$ is positive semidefinite, $\operatorname{tr}(GG^{\mathsf T})^{-1}=\|(GG^{\mathsf T})^{-1}\|_*$ is its nuclear (Schatten-1) norm, so this is the second moment of the nuclear norm of an inverse-Wishart matrix, Tropp–Webber Lemma B.2. Combined with the mean $r/(k-r-1)$ it gives the variance of $\|G^{\dagger}\|_F^2$, which is what deviation bounds for the Frobenius error of the randomized SVD require.
--
--   **Formalization Note.** The left side is written as $\|G^{\dagger}\|_F^4=(\|G^{\dagger}\|_F^2)^2$ with $G^{\dagger}$ = `pinvR`; on the null set where $GG^{\mathsf T}$ is singular `pinvR` is $0$, which does not affect the integral.
-- source:
--   J. A. Tropp, R. J. Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis, and applications*, 2023, https://arxiv.org/abs/2306.12418 (v1), Appendix B p. 51, Lemma B.2 (Inverse moment bounds), second formula: $\mathbb E\|(GG^*)^{-1}\|_*^2=\frac{r^2(k-r)-2r(r-1)}{(k-r)(k-r-1)(k-r-3)}$ for $r\le k-4$, using $\|(GG^*)^{-1}\|_*=\operatorname{tr}(GG^*)^{-1}=\|G^\dagger\|_F^2$ (cf. N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), Appendix A.2 p. 65, proof of Proposition A.5).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem pinv_frobenius_fourth_moment {r k : ℕ} (hrk : r + 4 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G)) ^ 2) (gaussianMatrix r k) ∧
    ∫ G, frobSq (pinvR (Matrix.of G)) ^ 2 ∂(gaussianMatrix r k)
      = ((r : ℝ) ^ 2 * ((k : ℝ) - r) - 2 * r * ((r : ℝ) - 1))
          / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by sorry
end GaussianMatrix
