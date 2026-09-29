-- Prove2me | Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
-- name    : OddPerfectNumber.local_sigma_factor_dvd_global
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T18:46:00.39304+00:00
-- url     : https://prove2.me/theorems/1eda4626-c24e-4a5e-a9d8-97cf727f7da4
-- title:
--   A local sigma factor divides the global divisor sum
-- statement:
--   For a nonzero natural n and a prime-support entry q of n, the geometric divisor sum associated with q and its factorization exponent divides the full divisor sum of n.
-- source:
--   This is the multiplicative sigma interface needed by finite-support certificates. Rewrite the divisor sum as ArithmeticFunction.sigma 1 n, use the Mathlib product formula over n.primeFactors, and apply Finset.dvd_prod_of_mem to the q factor.

import Mathlib

namespace OddPerfectNumber

theorem local_sigma_factor_dvd_global (n q : Nat)
    (hn : n ≠ 0) (hq : q ∈ n.primeFactors) :
    (∑ i ∈ Finset.range (n.factorization q + 1), q ^ i) ∣
      ∑ x ∈ n.divisors, x := by sorry

end OddPerfectNumber
