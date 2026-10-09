-- Prove2me | Theorems.Thm_GaussianMatrix_sMin_small_ball
-- name    : GaussianMatrix.sMin_small_ball
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:48:46.313692+00:00
-- url     : https://prove2.me/theorems/b9e3133a-dfe4-4c65-ab52-31d27c2c1f54
-- title:
--   Small-ball bound for the smallest singular value of a Gaussian matrix: $\mathbb P\{s_{\min}(A)\le s\}\le n\bigl(\frac{e\,n s^2}{N-n+1}\bigr)^{(N-n+1)/2}$
-- statement:
--   Let $A\in\mathbb R^{N\times n}$ be a standard Gaussian matrix with $1\le n\le N$, let $s_{\min}(A)=\inf_{\|x\|_2=1}\|Ax\|_2$, and put $d=N-n+1$. For every $s\ge0$ with $n s^2\le d$,
--   $$\mathbb P\bigl\{s_{\min}(A)\le s\bigr\}\ \le\ n\left(\frac{e\,n\,s^2}{d}\right)^{d/2}.$$
--
--   This small-ball estimate, with an explicit elementary constant, complements the Gaussian tail $\mathbb P\{s_{\min}\le\sqrt N-\sqrt n-u\}\le e^{-u^2/2}$: it gives polynomial decay of order $d=N-n+1$ as $s\to0$, with an explicit constant, and is what makes negative moments $\mathbb E\,s_{\min}(A)^{-2p}$ finite and explicitly bounded. The argument: if $s_{\min}\le s$ then some column $a_i$ of $A$ is within $\sqrt n\,s$ of the span of the other columns, that distance is a $\chi_d$ variable, and a chi-square lower tail plus a union bound over $i$ finish the proof.
--
--   **Formalization Note.** For a wide $k\times t$ Gaussian matrix $G$ the usual $\sigma_{\min}(G)$ equals $s_{\min}(G^{\mathsf T})$, so the wide form is this statement with $(N,n)=(t,k)$. The exponent $d/2$ is a real power.
-- source:
--   Combination of three published facts. (1) M. Rudelson, R. Vershynin, *The Littlewood–Offord problem and invertibility of random matrices*, Advances in Mathematics 218(2), 600–633, 2008, https://arxiv.org/abs/math/0703503, §3.3 p. 16, Lemma 3.5 (Invertibility via distance) and eq. (3.7): for any matrix with columns $X_k$ and $H_k=\operatorname{span}(X_j)_{j\ne k}$, $\|Ax\|_2\ge\max_k|x_k|\operatorname{dist}(X_k,H_k)$, so $s_{\min}(A)\le s$ forces $\operatorname{dist}(X_k,H_k)\le\sqrt n\,s$ for some $k$ (some unit $x$ has $|x_k|\ge n^{-1/2}$). (2) By rotational invariance (N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 55), conditionally on the other columns $\operatorname{dist}(X_k,H_k)^2\sim\chi^2_{N-n+1}$. (3) S. Dasgupta, A. Gupta, *An elementary proof of a theorem of Johnson and Lindenstrauss*, Random Structures & Algorithms 22(1), 60–65, 2003, https://doi.org/10.1002/rsa.10073, Lemma 2.2(a): $\mathbb P[\chi^2_d\le u]\le(eu/d)^{d/2}$ for $u\le d$. A union bound over the $n$ columns gives the stated bound. Compare the sharper-constant small-ball bound of N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), Appendix A.2 p. 64, Proposition A.3 (Chen–Dongarra).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem sMin_small_ball {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (s : ℝ) (hs : 0 ≤ s)
    (hsd : n * s ^ 2 ≤ (N : ℝ) - n + 1) :
    (gaussianMatrix N n) {A | sMin (Matrix.of A) ≤ s}
      ≤ ENNReal.ofReal (n * (Real.exp 1 * n * s ^ 2 / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) := by sorry
end GaussianMatrix
