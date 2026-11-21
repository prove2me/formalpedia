-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_interpolation_kernel
-- name    : MomentSearch.rakhmanov_interpolation_kernel
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T22:59:05.377433+00:00
-- url     : https://prove2.me/theorems/f58bec30-48eb-4ac2-8320-5ac10bdefe50
-- title:
--   Rakhmanov’s interpolation estimate with two capped reciprocal factors
-- statement:
--   Let $P$ have degree at most $k$ and absolute value at most one at the $N$ midpoint grid nodes $\zeta_j=-1+(2j-1)/N$, where $1\le k<N$. Write $r=\sqrt{1-k^2/N^2}$ and let $\mu'(x)$ be the density in (2.8). At each $x\in(-r,r)$ there are $0<M\le N/2$ and a point $y$ with $M\ge\mu'(x)$ and $|x-y|\le2/M$ such that
--   $$
--   |P(x)|\le A\sum_{j=1}^N\frac{1}{\max\{1,N|\zeta_j-x|\}\max\{1,M|\zeta_j-y|\}}
--   $$
--   for a universal positive constant $A$. This is the interpolation and equilibrium estimate (2.30). The numerical caps are absorbed into $A$. The bound $2/M$ follows from (2.23), the choice of a root with intervening mass at most $1/2$, and (2.26). The maxima in the denominators implement the caps even at coincident points.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Ann. of Math. 165 (2007), 55–88. https://annals.math.princeton.edu/2007/165-1/p03 §2.1, (2.8), and §2.2, (2.19)–(2.30), pp. 63–67.

import Mathlib

theorem MomentSearch.rakhmanov_interpolation_kernel :
    ∃ A : ℝ, 0 < A ∧
      ∀ N k : ℕ, 1 ≤ k → k < N →
      ∀ P : Polynomial ℝ, P.natDegree ≤ k →
      (∀ j : ℕ, 1 ≤ j → j ≤ N → |P.eval (-1 + (2 * (j : ℝ) - 1) / (N : ℝ))| ≤ 1) →
      ∀ r : ℝ, r = Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2) →
      ∀ x : ℝ, -r < x → x < r →
      ∃ M y : ℝ, 0 < M ∧ M ≤ (N : ℝ) / 2 ∧ |x - y| ≤ 2 / M ∧
        (N : ℝ) / Real.pi * Real.arctan ((N : ℝ) / (k : ℝ) *
          Real.sqrt (r ^ 2 - x ^ 2)) ≤ M ∧
        |P.eval x| ≤ A * (∑ j ∈ Finset.Icc 1 N,
          1 / (max 1 ((N : ℝ) * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - x|) *
            max 1 (M * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - y|))) := by sorry
