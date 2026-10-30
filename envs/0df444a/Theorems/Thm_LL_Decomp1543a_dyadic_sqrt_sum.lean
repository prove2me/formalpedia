-- Prove2me | Theorems.Thm_LL_Decomp1543a_dyadic_sqrt_sum
-- name    : LL_Decomp1543a.dyadic_sqrt_sum
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:51:10.415636+00:00
-- url     : https://prove2.me/theorems/54888baa-f6f3-44a3-b584-0beb0044abd2
-- title:
--   Sum of square roots of dyadic scales
-- statement:
--   For natural $N$, positive real $U,V$ and natural $J\ge1$ satisfying $2^{J-1}V\le N/U$, $\sum_{0\le j<J}\sqrt{2^jV}\le(2+\sqrt2)\sqrt{N/U}$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 174, first line. https://doi.org/10.4064/aa105-2-3

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem dyadic_sqrt_sum (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (J : ℕ) (hJ : 1 ≤ J)
    (hJV : 2 ^ (J - 1) * V ≤ N / U) :
    ∑ j ∈ range J, √(2 ^ j * V) ≤ (2 + √2) * √(N / U) := by sorry
end LL_Decomp1543a
