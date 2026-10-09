-- Prove2me | Theorems.Thm_GaussianMatrix_chi_square_lower_tail
-- name    : GaussianMatrix.chi_square_lower_tail
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:48:23.483548+00:00
-- url     : https://prove2.me/theorems/e05498a5-b9c2-4b12-8ca0-bd6cc5af3e18
-- title:
--   Chernoff lower tail of a chi-square variable: $\mathbb P\{\chi_d^2\le u\}\le(eu/d)^{d/2}$ for $0\le u\le d$
-- statement:
--   Let $g=(g_1,\dots,g_d)$ be a standard Gaussian vector in $\mathbb R^{d}$, $d\ge1$, so that $\chi_d^2=\sum_{i=1}^d g_i^2$ has the chi-square distribution with $d$ degrees of freedom. For every $u$ with $0\le u\le d$,
--   $$\mathbb P\bigl\{\chi_d^2\le u\bigr\}\ \le\ \Bigl(\frac{e\,u}{d}\Bigr)^{d/2}.$$
--
--   This is the elementary Chernoff (moment-generating-function) estimate for the lower tail of a chi-square variable (Dasgupta–Gupta, Lemma 2.2); it is the probabilistic input for small-ball estimates of distances of a Gaussian vector to a fixed subspace, and hence for the small-ball bound on the smallest singular value of a Gaussian matrix.
--
--   **Formalization Note.** The chi-square variable is realized as $\sum_i g_i^2$ under the product of $d$ standard normal measures on $\mathbb R^d$; the exponent $d/2$ is a real power. For $u=0$ the right side is $0$ and the left side is the probability of the null event $\{g=0\}$.
-- source:
--   S. Dasgupta, A. Gupta, *An elementary proof of a theorem of Johnson and Lindenstrauss*, Random Structures & Algorithms 22(1), 60–65, 2003, https://doi.org/10.1002/rsa.10073, Lemma 2.2(a): for $L\sim\chi^2_d$ and $\beta<1$, $\mathbb P[L\le\beta d]\le\beta^{d/2}\exp(d(1-\beta)/2)$; with $\beta=u/d$ this is $(u/d)^{d/2}e^{(d-u)/2}\le(eu/d)^{d/2}$ (the case $u=d$ is trivial). Also N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), Appendix A.3.1 p. 65, Proposition A.8 (chi-square moments) for the moment-generating-function route.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem chi_square_lower_tail {d : ℕ} (hd : 1 ≤ d) (u : ℝ) (hu : 0 ≤ u) (hud : u ≤ d) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) {g | ∑ i, g i ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / d) ^ ((d : ℝ) / 2)) := by sorry
end GaussianMatrix
