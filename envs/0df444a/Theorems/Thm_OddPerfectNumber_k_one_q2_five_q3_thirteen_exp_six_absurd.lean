-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_six_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_six_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:20:01.14241+00:00
-- url     : https://prove2.me/theorems/77d04939-f814-446a-9703-2c6500134a8c
-- title:
--   The q2=5 q3=13 exponent-six subcase is impossible
-- statement:
--   Under the canonical k=1 equations and support {3,5,13,q4} with q4 greater than 19531, the exponent-six case for the 5-component is impossible because sigma(5^6)=19531 forces an external prime factor.
-- source:
--   The accepted local sigma-factor divisibility theorem turns the exact factor 19531 of sigma(5^6) into a divisor of the global square-part sigma; the accepted finite-support certificate excludes it.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_external_nineteen_five_three_one_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_exp_six_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 6) :
    False := by sorry

end OddPerfectNumber
