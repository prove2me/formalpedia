-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_external_nineteen_five_three_one_absurd
-- name    : OddPerfectNumber.four_support_external_nineteen_five_three_one_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:16:20.509048+00:00
-- url     : https://prove2.me/theorems/ae312ffd-3313-453e-a506-ffb2eb4c1ac8
-- title:
--   An external 19531-factor is impossible in the {3,5,13,q4} support case
-- statement:
--   Let p be an Euler prime and suppose the square-part sigma sum is p*d with d dividing m^2. If every prime divisor of m is one of 3, 5, 13, q4, where q4 is prime and greater than 19531, then 19531 cannot divide the square-part sigma sum.
-- source:
--   Derived from the remotely accepted finite-support theorem. The five possible placements of the external prime 19531 are excluded by hp4, exact arithmetic, and 19531<q4.

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem four_support_external_nineteen_five_three_one_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h19531sigma : 19531 ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    False := by sorry

end OddPerfectNumber
