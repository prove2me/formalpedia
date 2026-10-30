-- Prove2me | Theorems.Thm_LL_Decomp1543a_dyadic_invsqrt_sum
-- name    : LL_Decomp1543a.dyadic_invsqrt_sum
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:51:22.095192+00:00
-- url     : https://prove2.me/theorems/f7dd89d0-30fa-495b-8561-9b1d29cd71ae
-- title:
--   Sum of reciprocal square roots of dyadic scales
-- statement:
--   For every positive real $V$ and natural $J$, $\sum_{0\le j<J}1/\sqrt{2^jV}\le(2+\sqrt2)/\sqrt V$. The sum is empty when $J=0$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 174, first two lines. https://doi.org/10.4064/aa105-2-3

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem dyadic_invsqrt_sum (V : ℝ) (hV : 0 < V) (J : ℕ) :
    ∑ j ∈ range J, 1 / √(2 ^ j * V) ≤ (2 + √2) / √V := by sorry
end LL_Decomp1543a
