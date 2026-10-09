-- Prove2me | Theorems.Thm_GaussianMatrix_pinv_frobenius_moment
-- name    : GaussianMatrix.pinv_frobenius_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:39:08.875819+00:00
-- url     : https://prove2.me/theorems/8e41ee10-92ad-440f-8e4e-bff48f944959
-- title:
--   Expected squared Frobenius norm of a pseudo-inverted Gaussian matrix: $\mathbb E\|G^{\dagger}\|_F^2=\frac{r}{k-r-1}$
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix with $k-r\ge2$, and let $G^{\dagger}=G^{\mathsf T}(GG^{\mathsf T})^{-1}$ be its pseudoinverse. Then $\|G^{\dagger}\|_F^2$ is integrable and
--   $$\mathbb E\,\|G^{\dagger}\|_F^2=\frac{r}{k-r-1}.$$
--
--   In the notation of Halko–Martinsson–Tropp, $G$ is $k\times(k+p)$ and the right-hand side reads $k/(p-1)$: this is the inverse moment that enters the expected Frobenius error bound $\bigl(1+\tfrac{k}{p-1}\bigr)^{1/2}\|\Sigma_2\|_F$ of the randomized SVD, and more generally every expected-error bound for Gaussian sketching with oversampling.
--
--   **Formalization Note.** $G^{\dagger}$ is `pinvR`, which is $0$ on the null set where $GG^{\mathsf T}$ is singular; the conclusion is the conjunction of integrability and the identity. No lower bound on $r$ is needed ($r=0$ gives $0=0$).
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 55, Proposition 10.2 eq. (10.3) ($k\times(k+p)$, $p\ge2$) and Appendix A.2 p. 65, Proposition A.5 ($m\times n$, $n-m\ge2$: $\mathbb E\|G^\dagger\|_F^2=\frac{m}{n-m-1}$); also J. A. Tropp, R. J. Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis, and applications*, 2023, https://arxiv.org/abs/2306.12418 (v1), Appendix B p. 51, Lemma B.2 (trace of the first formula).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem pinv_frobenius_moment {r k : ℕ} (hrk : r + 2 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G))) (gaussianMatrix r k) ∧
    ∫ G, frobSq (pinvR (Matrix.of G)) ∂(gaussianMatrix r k) = (r : ℝ) / ((k : ℝ) - r - 1) := by sorry
end GaussianMatrix
