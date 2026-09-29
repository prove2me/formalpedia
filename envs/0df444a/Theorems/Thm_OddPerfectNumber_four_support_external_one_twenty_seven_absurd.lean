-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_external_one_twenty_seven_absurd
-- name    : OddPerfectNumber.four_support_external_one_twenty_seven_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:04:59.289239+00:00
-- url     : https://prove2.me/theorems/f31ff2c7-34ba-4812-b5d7-43a099972c2b
-- title:
--   An external 127-factor is impossible in the {3,5,19,q4} support case
-- statement:
--   Let p be an Euler prime and suppose the square-part sigma sum is p*d with d dividing m^2. If every prime divisor of m is one of 3, 5, 19, q4, where q4 is prime and greater than 127, then 127 cannot divide the square-part sigma sum.
-- source:
--   Derived from the accepted finite-support theorem. The prime 127 cannot be p by p % 4 = 1, cannot be 3,5,19 numerically, and cannot equal q4 because 127<q4.

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem four_support_external_one_twenty_seven_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 127 < q4)
    (h127sigma : 127 ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    False := by sorry

end OddPerfectNumber
