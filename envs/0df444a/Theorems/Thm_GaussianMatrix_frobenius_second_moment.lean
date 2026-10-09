-- Prove2me | Theorems.Thm_GaussianMatrix_frobenius_second_moment
-- name    : GaussianMatrix.frobenius_second_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:27:44.938489+00:00
-- url     : https://prove2.me/theorems/b410404c-99ca-44ca-9b3f-57cb7ea23e5c
-- title:
--   Expected squared Frobenius norm of a scaled Gaussian matrix: $\mathbb E\|S\Gamma T\|_F^2=\|S\|_F^2\|T\|_F^2$
-- statement:
--   Fix matrices $S\in\mathbb R^{a\times p}$ and $T\in\mathbb R^{m\times n}$ and let $\Gamma\in\mathbb R^{p\times m}$ be a standard Gaussian matrix. Then
--   $$\mathbb E\,\|S\,\Gamma\,T\|_F^2=\|S\|_F^2\,\|T\|_F^2 .$$
--
--   This second-moment identity is the first of the Gaussian moment bounds (Halko–Martinsson–Tropp Proposition 10.1, eq. (10.1); Tropp–Webber Lemma B.1). It is the identity that produces the factor $\|\Sigma_2\|_F^2\,\mathbb E\|\Omega_1^{\dagger}\|_F^2$ in the expected Frobenius error of the randomized SVD, and with $S=I$, $T=I$ it says $\mathbb E\|\Gamma\|_F^2=pm$.
--
--   **Formalization Note.** The expectation is a Lebesgue integral against $\gamma_{p,m}$; the integrand is a polynomial in the entries of $\Gamma$ and hence integrable.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 55, Proposition 10.1, eq. (10.1), and Appendix A.1 p. 64, Proposition A.1; also J. A. Tropp, R. J. Webber, *Randomized algorithms for low-rank matrix approximation: design, analysis, and applications*, 2023, https://arxiv.org/abs/2306.12418 (v1), Appendix B p. 47, Lemma B.1, first equality.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem frobenius_second_moment {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, frobSq (S * Matrix.of G * T) ∂(gaussianMatrix p m) = frobSq S * frobSq T := by sorry
end GaussianMatrix
