-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_1093_role
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_1093_role
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T21:46:54.941981+00:00
-- url     : https://prove2.me/theorems/f2be5f3d-cc54-4d83-ba6b-68784480acb2
-- title:
--   The exponent-six 3-component forces the 1093 role
-- statement:
--   In the q2=5, q3=19 four-support equations, if the 3-component has exponent 6, then the forced factor 1093 of sigma(3^6) must occupy either the Euler-prime slot p or the fourth support-prime slot q4.
-- source:
--   The accepted local sigma-factor divisibility theorem makes 1093 divide the global divisor sum. The accepted finite-support restriction forces 1093 to equal p, 3, 5, 19, or q4; exact arithmetic excludes the middle three cases.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp3_six_1093_role (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6) :
    p = 1093 ∨ q4 = 1093 := by sorry

end OddPerfectNumber
