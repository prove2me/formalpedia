-- Prove2me | Theorems.Thm_GaussianMatrix_dist_col_span_small_ball
-- name    : GaussianMatrix.dist_col_span_small_ball
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:51:33.756977+00:00
-- url     : https://prove2.me/theorems/b0c995e5-b56f-469e-9b98-567d05ddc45c
-- title:
--   Small-ball bound for the distance of a Gaussian column to the span of the others: $\mathbb P\{\operatorname{dist}(a_j,H_j)^2\le u\}\le (eu/(N-n+1))^{(N-n+1)/2}$
-- statement:
--   Let $1\le n\le N$ and let $A$ be an $N\times n$ random matrix with independent standard normal entries, with columns $a_1,\dots,a_n$. Fix a column index $j$ and let $H_j=\operatorname{span}\{a_i:i\ne j\}$, with
--   $$\operatorname{dist}(a_j,H_j)=\inf_{x\in\mathbb R^n,\ x_j=1}\|Ax\|_2 .$$
--   Then for every real $u$ with $0\le u\le N-n+1$,
--   $$\mathbb P\big\{\operatorname{dist}(a_j,H_j)^2\le u\big\}\;\le\;\Big(\frac{e\,u}{N-n+1}\Big)^{(N-n+1)/2}.$$
--
--   Conditionally on the other columns, $a_j$ is a standard Gaussian vector independent of $H_j$, a subspace of dimension at most $n-1$; the squared distance of $a_j$ to it dominates a $\chi^2$ variable with $N-n+1$ degrees of freedom, whose lower tail obeys the stated bound. Integrating over the other columns gives the claim.
--
--   Combined with the deterministic reduction $\sigma_{\min}(A)\le s\Rightarrow\exists j,\ \operatorname{dist}(a_j,H_j)\le\sqrt n s$ and a union bound over $j$, this yields the small-ball estimate $\mathbb P\{\sigma_{\min}(A)\le s\}\le n\,(e n s^2/(N-n+1))^{(N-n+1)/2}$.
--
--   **Formalization Note.** The law of $A$ is `gaussianMatrix N n` (a product over rows of product measures); the event is written with the explicit infimum, and the probability of a possibly non-measurable set is the outer measure (the set is in fact measurable). The dimension of $H_j$ may drop below $n-1$; the bound holds regardless since the degrees of freedom only increase.
-- source:
--   standard fact: for a standard Gaussian vector g in R^N independent of a subspace H with dim H ≤ n−1, dist(g,H)^2 stochastically dominates χ²_{N−n+1}; combined with the χ² lower tail P{χ²_d ≤ u} ≤ (eu/d)^{d/2} (cf. Rudelson–Vershynin, Adv. Math. 218 (2008), §3; Laurent–Massart, Ann. Statist. 28 (2000), Lemma 1).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem dist_col_span_small_ball {N n : ℕ} (hnN : n ≤ N) (j : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hud : u ≤ (N : ℝ) - n + 1) :
    (gaussianMatrix N n) {A | (⨅ x : {x : Fin n → ℝ // x j = 1},
        Real.sqrt ((Matrix.of A *ᵥ x.1) ⬝ᵥ (Matrix.of A *ᵥ x.1))) ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / ((N : ℝ) - n + 1)) ^ (((N : ℝ) - n + 1) / 2)) := by sorry

end GaussianMatrix
