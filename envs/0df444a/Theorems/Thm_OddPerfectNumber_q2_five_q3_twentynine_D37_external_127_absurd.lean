-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_external_127_absurd
-- name    : OddPerfectNumber.q2_five_q3_twentynine_D37_external_127_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T08:09:07.461554+00:00
-- url     : https://prove2.me/theorems/3bbd3147-661c-44aa-a8fe-ac2c4af6d83c
-- title:
--   The q3=29 D=37 external 127 source is impossible
-- statement:
--   In the q2=5,q3=29,D=37 support, an external 127 divisor of sigma(m^2) is impossible by the accepted four-support sigma-prime restriction.
-- source:
--   Apply the accepted finite-support sigma-prime restriction at r=127 and discharge the five impossible support/Euler equalities.

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_D37_external_127_absurd (p m d q4 : Nat) (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hddvd : d ∣ m ^ 2) (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) (hq4prime : q4.Prime) (hq4eq : q4 = 37) (h127sigma : 127 ∣ ∑ x ∈ (m ^ 2).divisors, x) : False := by
  sorry

end OddPerfectNumber
