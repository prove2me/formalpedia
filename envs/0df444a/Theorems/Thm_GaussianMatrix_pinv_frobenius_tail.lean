-- Prove2me | Theorems.Thm_GaussianMatrix_pinv_frobenius_tail
-- name    : GaussianMatrix.pinv_frobenius_tail
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:43:25.171556+00:00
-- url     : https://prove2.me/theorems/53a7883f-cc32-49c4-afea-5fe577da2469
-- title:
--   Halko–Martinsson–Tropp tail bound for $\|G^{\dagger}\|_F$: $\mathbb P\{\|G^{\dagger}\|_F^2>\frac{12r}{k-r}\,t\}\le 4t^{-(k-r)/2}$
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix with $k-r\ge4$, and let $G^{\dagger}=G^{\mathsf T}(GG^{\mathsf T})^{-1}$. For every $t\ge1$,
--   $$\mathbb P\Bigl\{\|G^{\dagger}\|_F^2>\frac{12\,r}{k-r}\cdot t\Bigr\}\ \le\ 4\,t^{-(k-r)/2}.$$
--
--   This is the large-deviation bound for the Frobenius norm of a pseudo-inverted Gaussian matrix, which Halko–Martinsson–Tropp introduced (Theorem A.6; stated as Proposition 10.4 eq. (10.5) in the form $\mathbb P\{\|G^{\dagger}\|_F\ge\sqrt{12k/p}\,t\}\le4t^{-p}$) to prove deviation bounds for the Frobenius error of the randomized SVD. Unlike the spectral-norm tail, it is proved through the bidiagonal (Householder) model of a Gaussian matrix and chi-square moment estimates.
--
--   **Formalization Note.** The event is $\{\tfrac{12r}{k-r}t<\|G^{\dagger}\|_F^2\}$ with `pinvR` as $G^{\dagger}$; the exponent $-(k-r)/2$ is a real power (`rpow`) of $t\ge1$.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), Appendix A.3 p. 65, Theorem A.6: for an $m\times n$ standard Gaussian $G$ with $n-m\ge4$ and $t\ge1$, $\mathbb P\{\|G^\dagger\|_F^2>\frac{12m}{n-m}\cdot t\}\le4t^{-(n-m)/2}$ (equivalently §10.1 p. 56, Proposition 10.4 eq. (10.5)).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem pinv_frobenius_tail {r k : ℕ} (hrk : r + 4 ≤ k) (t : ℝ) (ht : 1 ≤ t) :
    (gaussianMatrix r k) {G | 12 * (r : ℝ) / ((k : ℝ) - r) * t < frobSq (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal (4 * t ^ (-(((k : ℝ) - r) / 2))) := by sorry
end GaussianMatrix
