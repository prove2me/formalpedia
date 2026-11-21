-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_grid_kernel_sum
-- name    : MomentSearch.rakhmanov_grid_kernel_sum
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T22:59:07.720364+00:00
-- url     : https://prove2.me/theorems/3f86a5c6-e0ef-496e-a348-f165659df549
-- title:
--   Logarithmic bound for the two-factor sum on a uniform grid
-- statement:
--   Take the $N$ midpoint grid nodes of spacing $2/N$, where $N\ge1$. For any real $x,y$ and $0<M\le N/2$ with $|x-y|\le2/M$, the finite sum
--   $$
--   \sum_{j=1}^N\frac{1}{\max\{1,N|\zeta_j-x|\}\max\{1,M|\zeta_j-y|\}}
--   $$
--   is at most $D\log_2(N/M)$ for a universal positive constant $D$. This is the discrete summation step of (2.31)–(2.34), with conservative caps. One can first bound $\max\{1,M|\zeta_j-x|\}$ by $3\max\{1,M|\zeta_j-y|\}$ using the triangle inequality. On each side of $x$, grid spacing bounds the sum of the resulting factors by a harmonic contribution up to scale $1/M$ and a reciprocal-square tail beyond it.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Ann. of Math. 165 (2007), 55–88. https://annals.math.princeton.edu/2007/165-1/p03 §2.2, (2.30)–(2.34), pp. 67–68.

import Mathlib

theorem MomentSearch.rakhmanov_grid_kernel_sum :
    ∃ D : ℝ, 0 < D ∧
      ∀ N : ℕ, 0 < N → ∀ M x y : ℝ, 0 < M → M ≤ (N : ℝ) / 2 → |x - y| ≤ 2 / M →
        (∑ j ∈ Finset.Icc 1 N,
          1 / (max 1 ((N : ℝ) * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - x|) *
            max 1 (M * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - y|))) ≤
          D * Real.logb 2 ((N : ℝ) / M) := by sorry
