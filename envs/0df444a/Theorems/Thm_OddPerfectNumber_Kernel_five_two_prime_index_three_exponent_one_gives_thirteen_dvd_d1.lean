-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1
-- name    : OddPerfectNumber.Kernel.five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T12:38:57.957583+00:00
-- url     : https://prove2.me/theorems/bcd032e7-5cbd-4a31-8a4f-8b3ebac0f2e0
-- title:
--   In the k=5 two-prime residual, if 3 divides m exactly once then 13 divides d1
-- statement:
--   Suppose p is the Euler prime of an odd perfect number candidate satisfying the k=5 Dris equations with a square-free index d1^2*q*r for distinct primes q < r, neither of which is 3.  If 3 occurs in m to exactly the first power, then 13 divides d1.
-- source:
--   MECHANISM.  3 | m, so 3 occurs among the prime-power factors of m^2 and contributes the local factor sigma(3^2) = 1 + 3 + 9 = 13 to the divisor sum.  Since sigma(m^2) = p^5 * d1^2 * q * r, the prime 13 divides that product.  Now 13 is not 3, and 13 divides none of p, q, r: 13 = 13 is not 1 (mod 4) so p != 13 is not forced by hp4 alone, but the established first-equation congruences give p = 5 (mod 48) and q, r = 7 (mod 24), and 13 = 13 (mod 48) and 13 = 13 (mod 24) match neither.  Hence 13 | d1^2, and since 13 is prime this gives 13 | d1.
--
--   AUDIT.  sigma(3^2) = 13 exactly (divisors of 9 are 1, 3, 9).  13 mod 48 = 13 and 13 mod 24 = 13, so 13 is excluded from both the Euler prime and both index primes under the congruences proved for this branch.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_index_three_exponent_one_gives_thirteen_dvd_d1 (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m)
    (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3)
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r)))
    (he : m.factorization 3 = 1) :
    Dvd.dvd 13 d1 := by
  sorry

end OddPerfectNumber.Kernel
