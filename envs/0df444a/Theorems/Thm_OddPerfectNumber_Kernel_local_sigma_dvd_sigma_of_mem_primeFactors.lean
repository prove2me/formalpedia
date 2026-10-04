-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_local_sigma_dvd_sigma_of_mem_primeFactors
-- name    : OddPerfectNumber.Kernel.local_sigma_dvd_sigma_of_mem_primeFactors
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:47:30.207719+00:00
-- url     : https://prove2.me/theorems/40498f43-821b-4be8-b7c0-e27515dde1c5
-- title:
--   A local divisor-sum factor of a prime dividing n divides the divisor sum of n squared
-- statement:
--   Let n be a nonzero natural number and let l be a prime dividing n. Then the geometric sum 1 plus l plus l squared up to l raised to twice the exponent of l in n divides the sum of the divisors of n squared. This is the multiplicativity step behind the prime closure: because d1 divides m, every prime of d1 has its own local divisor-sum factor inside sigma of m squared, and that factor divides the second Dris right-hand side p to the fifth times d1 squared times qC times qD.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem local_sigma_dvd_sigma_of_mem_primeFactors {n l : Nat} (hn : n != 0)
    (hl : l ∈ n.primeFactors) :
    Dvd.dvd (∑ i ∈ Finset.range (2 * n.factorization l + 1), l ^ i)
      (∑ d ∈ (n ^ 2).divisors, d) := by
  sorry

end OddPerfectNumber.Kernel
