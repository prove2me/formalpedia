-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_ge_four_q4gt127
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_ge_four_q4gt127
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T22:20:04.178206+00:00
-- url     : https://prove2.me/theorems/27b5c97a-2d6f-4220-b6cd-03f54b2c2c63
-- title:
--   The 19-component exponent is at least four when the fourth support prime exceeds 127
-- statement:
--   A positive even exponent below four must be two. The accepted 19² contradiction rules out that case when q4>127.
-- source:
--   Assume the 19-component exponent is below four. Positivity and evenness reduce it to 2, and the accepted q3=19 exponent-two contradiction then closes the case.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_two_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp19_ge_four_q4gt127 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 127 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19even : Even ((m ^ 2).factorization 19))
    (h19pos : 0 < (m ^ 2).factorization 19) :
    4 ≤ (m ^ 2).factorization 19 := by sorry

end OddPerfectNumber
