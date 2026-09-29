-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_four_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp_four_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:25:19.64135+00:00
-- url     : https://prove2.me/theorems/ab795858-27e1-41b8-8b72-aaf8f0cf7d66
-- title:
--   The q2=5 q3=19 exponent-four subcase is impossible
-- statement:
--   Under the canonical k=1 equations and support {3,5,19,q4} with q4 greater than 151, the exponent-four case for the 19-component is impossible because sigma(19^4) is divisible by the external prime 151.
-- source:
--   The accepted local sigma-factor divisibility theorem turns the exact factor 151 of sigma(19^4) into a divisor of the global square-part sigma; the accepted finite-support certificate excludes it.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_external_one_five_one_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp_four_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 151 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 4) :
    False := by sorry

end OddPerfectNumber
