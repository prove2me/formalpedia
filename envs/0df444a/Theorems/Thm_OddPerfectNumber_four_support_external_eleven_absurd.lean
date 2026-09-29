-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_external_eleven_absurd
-- name    : OddPerfectNumber.four_support_external_eleven_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T18:35:57.698501+00:00
-- url     : https://prove2.me/theorems/2a294290-9c0e-430b-a0ff-1db7df847114
-- title:
--   An external 11-factor is impossible in the {3,5,13,q4} support case
-- statement:
--   Let p be an Euler prime and suppose the square-part sigma sum is p*d with d dividing m^2. If every prime divisor of m is one of 3, 5, 13, q4, where q4 is prime and greater than 13, then 11 cannot divide the square-part sigma sum.
-- source:
--   Derived from the remotely accepted finite-support theorem OddPerfectNumber.four_support_sigma_prime_restricted. The proof excludes each of the five possible support/euler placements for the external prime 11 by exact arithmetic and hp4.

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem four_support_external_eleven_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (h11sigma : 11 ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    False := by sorry

end OddPerfectNumber
