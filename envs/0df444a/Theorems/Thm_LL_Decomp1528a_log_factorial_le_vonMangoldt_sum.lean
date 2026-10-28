-- Prove2me | Theorems.Thm_LL_Decomp1528a_log_factorial_le_vonMangoldt_sum
-- name    : LL_Decomp1528a.log_factorial_le_vonMangoldt_sum
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:14:44.384283+00:00
-- url     : https://prove2.me/theorems/a628ec5a-9f53-4b58-aa15-15f805a0b0de
-- title:
--   Factorial bounded by the weighted von Mangoldt sum
-- statement:
--   For every natural number $n$, $\log(n!)\le n\sum_{m=1}^{n}\frac{\Lambda(m)}{m}$, where $\Lambda$ is the von Mangoldt function and the sum is empty for $n=0$.
-- source:
--   Montgomery and Vaughan, Multiplicative Number Theory I, Section 2.2; lab unit U-1528. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem log_factorial_le_vonMangoldt_sum (n : ℕ) :
    log (n.factorial : ℝ) ≤ (n : ℝ) * ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m := by sorry
end LL_Decomp1528a
