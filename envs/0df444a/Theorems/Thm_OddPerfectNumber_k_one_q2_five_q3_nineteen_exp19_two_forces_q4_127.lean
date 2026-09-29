-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_forces_q4_127
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_forces_q4_127
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:00:55.632002+00:00
-- url     : https://prove2.me/theorems/80b12dc5-57d4-4cb6-a6ec-e9ab1382e0b5
-- title:
--   The exponent-two 19-component forces fourth support prime 127
-- statement:
--   The accepted 127 role theorem gives p=127 or q4=127. The p=127 case makes 64 divide the odd square m² and is impossible, so q4=127.
-- source:
--   Apply the accepted 127 role theorem, eliminate its Euler-prime alternative with the accepted odd-square parity lemma, and return the support-prime alternative.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p127_hprod_odd_square_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp19_two_forces_q4_127 (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2) :
    q4 = 127 := by sorry

end OddPerfectNumber
