-- Prove2me | Theorems.Thm_LL_Decomp1528a_log_factorial_eq_vonMangoldt
-- name    : LL_Decomp1528a.log_factorial_eq_vonMangoldt
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:14:17.263951+00:00
-- url     : https://prove2.me/theorems/31e82a7a-e285-4e2e-ad2d-d42be9d3390e
-- title:
--   Chebyshev identity for the logarithm of a factorial
-- statement:
--   For every natural number $n$, $\log(n!)=\sum_{m=1}^{n}\Lambda(m)\lfloor n/m\rfloor$, where $\Lambda(m)=\log p$ if $m$ is a positive power of a prime $p$, and $\Lambda(m)=0$ otherwise.
-- source:
--   Ingham, The Distribution of Prime Numbers, Theorem 7 proof; Montgomery and Vaughan, Multiplicative Number Theory I, Section 2.2. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem log_factorial_eq_vonMangoldt (n : ℕ) :
    log (n.factorial : ℝ) =
      ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m * ((n / m : ℕ) : ℝ) := by sorry
end LL_Decomp1528a
