-- Prove2me | Theorems.Thm_MetricGeometry_dist_sq_le_card_mul_sum_dist_sq
-- name    : MetricGeometry.dist_sq_le_card_mul_sum_dist_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T09:25:23.890644+00:00
-- url     : https://prove2.me/theorems/d13ecf14-5b9c-4c48-ace3-42db5f350b13
-- title:
--   Squared endpoint distance is at most the length of a chain times its squared increments
-- statement:
--   Let $x_0,x_1,\dots,x_n$ be points of a metric space. Then
--   $$d(x_0,x_n)^2\ \le\ n\sum_{i=0}^{n-1} d(x_i,x_{i+1})^2 .$$
--
--   **Role.** This is the discrete Cauchy--Schwarz estimate that converts a chain of short steps into a lower bound for a sum of *squared* increments. It is the combinatorial heart of the Poincaré inequality for the Korevaar--Schoen approximate energies: a map whose values at two points differ by $a$ must, along any chain of $n$ steps joining them, have squared increments summing to at least $a^2/n$, and integrating that over a family of parallel chains is what forces the approximate energy to stay bounded away from zero.
--
--   **Proof.** The triangle inequality along the chain gives $d(x_0,x_n)\le\sum_{i<n}d(x_i,x_{i+1})$, and the Cauchy--Schwarz inequality (Chebyshev's sum inequality in the diagonal case) gives $\bigl(\sum_{i<n}t_i\bigr)^2\le n\sum_{i<n}t_i^2$ for real $t_i$. Combining the two, and using that squaring is monotone on nonnegative reals, yields the claim.
-- source:
--   The discrete Cauchy--Schwarz step in the Poincare inequality for approximate energies, N. Korevaar and R. Schoen, Sobolev spaces and harmonic maps for metric space targets, Comm. Anal. Geom. 1 (1993), Section 1.

import Mathlib

namespace MetricGeometry

universe u

theorem dist_sq_le_card_mul_sum_dist_sq {X : Type u} [PseudoMetricSpace X]
    (x : ℕ → X) (n : ℕ) :
    dist (x 0) (x n) ^ 2
      ≤ (n : ℝ) * ∑ i ∈ Finset.range n, dist (x i) (x (i + 1)) ^ 2 := by sorry

end MetricGeometry
