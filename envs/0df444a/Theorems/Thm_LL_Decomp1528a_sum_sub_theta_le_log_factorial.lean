-- Prove2me | Theorems.Thm_LL_Decomp1528a_sum_sub_theta_le_log_factorial
-- name    : LL_Decomp1528a.sum_sub_theta_le_log_factorial
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:12:48.071613+00:00
-- url     : https://prove2.me/theorems/cbe825c5-7daf-4cf1-a0a1-b521fda03474
-- title:
--   Legendre lower bound using the Chebyshev function
-- statement:
--   For every natural number $n$, $n\sum_{p\le n}\frac{\log p}{p}-\theta(n)\le\log(n!)$, where $\theta(n)=\sum_{p\le n}\log p$ and the sums run over primes.
-- source:
--   Ingham, The Distribution of Prime Numbers, Theorem 7. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem sum_sub_theta_le_log_factorial (n : ℕ) :
    (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p - θ n ≤ log (n.factorial : ℝ) := by sorry
end LL_Decomp1528a
