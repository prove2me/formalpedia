-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_role
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T22:55:10.64139+00:00
-- url     : https://prove2.me/theorems/8237a553-8e72-4ac6-8e3e-68533379a4ef
-- title:
--   The exponent-two 19-component forces p=127 or q4=127
-- statement:
--   The local sigma factor for 19^2 is divisible by 127. Support closure restricts 127 to the Euler prime or the fourth support prime.
-- source:
--   Use the accepted local sigma divisibility and four-support restriction. Evaluate 127 | (1+19+19^2), eliminate the three fixed-support alternatives, and orient the remaining equalities.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp19_two_role (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2) :
    p = 127 ∨ q4 = 127 := by sorry

end OddPerfectNumber
