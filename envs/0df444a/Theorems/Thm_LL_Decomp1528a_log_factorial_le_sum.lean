-- Prove2me | Theorems.Thm_LL_Decomp1528a_log_factorial_le_sum
-- name    : LL_Decomp1528a.log_factorial_le_sum
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:12:36.353833+00:00
-- url     : https://prove2.me/theorems/40f40bc4-e2e1-4109-b2f3-33655f345c0f
-- title:
--   Legendre upper bound for the logarithm of a factorial
-- statement:
--   For every natural number $n$, $\log(n!)\le n\sum_{p\le n}\frac{\log p}{p}+n\sum_{p\le n}\frac{\log p}{p(p-1)}$, where both sums run over primes.
-- source:
--   Legendre formula; Ingham, The Distribution of Prime Numbers, Theorem 7; Rosser and Schoenfeld 1962, p. 70 style. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem log_factorial_le_sum (n : ℕ) :
    log (n.factorial : ℝ) ≤
      (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p +
        (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) := by sorry
end LL_Decomp1528a
