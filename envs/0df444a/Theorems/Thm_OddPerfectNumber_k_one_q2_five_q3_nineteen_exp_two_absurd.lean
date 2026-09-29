-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_two_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp_two_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:08:23.97535+00:00
-- url     : https://prove2.me/theorems/bb3d9404-2977-4eed-9564-13ed1815006c
-- title:
--   The q2=5 q3=19 exponent-two large-q4 subcase is impossible
-- statement:
--   In the canonical k=1 equations, suppose every prime divisor of m is one of 3, 5, 19, q4 with q4>127, and the exponent of 19 in m^2 is exactly 2. Then this four-support subcase is impossible.
-- source:
--   The accepted local sigma-factor theorem supplies the 19^2 geometric factor. Its exact value is 381=3*127, and the accepted external-127 support certificate rules out 127 from the Euler or support slots.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_external_one_twenty_seven_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp_two_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 127 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2) :
    False := by sorry

end OddPerfectNumber
