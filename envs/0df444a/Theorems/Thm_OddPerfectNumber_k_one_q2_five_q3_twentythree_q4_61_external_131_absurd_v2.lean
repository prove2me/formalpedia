-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_61_external_131_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_61_external_131_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T19:27:10.761971+00:00
-- url     : https://prove2.me/theorems/39c6ad0c-1b85-4bc5-9f69-6d54f8b949d5
-- title:
--   An external 131-source is impossible at q4=61 v2
-- statement:
--   In support {3,5,23,61}, a prime factor 131 of the square-part sigma is impossible because it is neither the Euler prime nor a support prime; p=131 is also excluded by p≡1 mod 4.
-- source:
--   Apply the accepted finite-support sigma-prime restriction to r=131 and discharge the five impossible equalities by exact arithmetic.

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_q4_61_external_131_absurd_v2 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4eq : q4 = 61)
    (h131sigma : 131 ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  sorry

end OddPerfectNumber
