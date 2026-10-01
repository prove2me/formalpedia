-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_ferm_order_ne_one_of_even_exp
-- name    : OddPerfectNumber.Kernel.ferm_order_ne_one_of_even_exp
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T18:32:17.629398+00:00
-- url     : https://prove2.me/theorems/fba2a185-9208-42c9-9e26-e92beebc7873
-- title:
--   A prime of exponent order two admits no odd order, so a squared divisor sum is not divisible by it
-- statement:
--   Let p be a prime whose predecessor p minus one is a power of two, so that p is a Fermat prime, and let m be a natural number with p not dividing m. Then p does not divide the divisor sum of m squared. Indeed every exponent in the prime factorization of m squared is even, say e = 2 * k, so the local divisor sum is 1 + t + ... + t^(2k) with 2k+1 odd terms. If p divided that sum, then t would have odd multiplicative order modulo p; but a group of order a power of two has no element of odd order other than the identity, and t = 1 modulo p forces p to divide 2k+1, impossible for p at least five. This is the standard reason a Fermat prime cannot divide a divisor sum of a square to which it is coprime.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem ferm_order_ne_one_of_even_exp {p m t : Nat} (hp : p.Prime) (hpm : ¬ Dvd.dvd p m)
    (hfer : ∃ v : ℕ, p - 1 = 2 ^ v) (hq : p ≥ 5) (htd : Dvd.dvd t (m ^ 2))
    (he : 0 < (m ^ 2).factorization t) :
    ¬ Dvd.dvd p (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) := by
  sorry

end OddPerfectNumber.Kernel
