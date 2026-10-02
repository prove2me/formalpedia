-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_dris_five_abundancy_of_square_part
-- name    : OddPerfectNumber.Kernel.dris_five_abundancy_of_square_part
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T22:03:21.192986+00:00
-- url     : https://prove2.me/theorems/2a458c03-649f-4624-afcd-8bb30f440934
-- title:
--   The two Dris equations at exponent five fix the abundancy of the square part
-- statement:
--   Let p be a natural number, let m and s be natural numbers, and suppose the two Dris equations hold: twice m squared equals the sum of the divisors of p to the fifth times s, and the sum of the divisors of m squared equals p to the fifth times s. Assume m is nonzero and s is nonzero. Then sigma(m^2) times 2 equals m squared times p to the fifth times the sum of the divisors of p to the fifth. Equivalently the abundancy of the square part, sigma(m^2) divided by m squared, is forced to be twice p to the fifth divided by the sum of the divisors of p to the fifth. This is the only invariant of the two equations that involves neither the square factor of the index nor the two odd-multiplicity primes of the index, since the index s cancels; it is therefore the natural target for any argument that must bypass the index.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem dris_five_abundancy_of_square_part (p m s : Nat) (hm : m ≠ 0) (hs : s ≠ 0)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    2 * (∑ d ∈ (m ^ 2).divisors, d) =
      m ^ 2 * (p ^ 5 * (∑ d ∈ (p ^ 5).divisors, d)) := by
  sorry

end OddPerfectNumber.Kernel
