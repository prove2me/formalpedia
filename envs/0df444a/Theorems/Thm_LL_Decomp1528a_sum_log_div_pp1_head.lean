-- Prove2me | Theorems.Thm_LL_Decomp1528a_sum_log_div_pp1_head
-- name    : LL_Decomp1528a.sum_log_div_pp1_head
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:13:06.347654+00:00
-- url     : https://prove2.me/theorems/751521d9-83e1-43f6-90ad-54a369dd5134
-- title:
--   Explicit bound for the prime sum through $1000$
-- statement:
--   The finite sum over primes satisfies $\sum_{p\le1000}\frac{\log p}{p(p-1)}\le0.7545$.
-- source:
--   Rosser and Schoenfeld 1962, equation 2.11 and the constant E on p. 70; the bound 0.7545 is the lab leaf. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem sum_log_div_pp1_head :
    ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.7545 := by sorry
end LL_Decomp1528a
