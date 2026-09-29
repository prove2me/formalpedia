-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_two_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T22:52:16.810104+00:00
-- url     : https://prove2.me/theorems/810c845e-49ec-421d-932a-fd0550bcd284
-- title:
--   The q2=5 q3=19 exponent-two 3-component subcase is impossible
-- statement:
--   The accepted exponent-two role theorem forces p=13. Then the half-successor support lemma forces 7 to divide m, contradicting the support restriction 3,5,19,q4 with q4>19.
-- source:
--   Apply the accepted p=13 role theorem, derive 7∣m from 7∣(13+1)/2, extract 7 from m.primeFactors, and eliminate all four support alternatives by norm_num/omega.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_role
import Theorems.Thm_OddPerfectNumber_k_one_half_successor_support

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp3_two_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2) :
    False := by sorry

end OddPerfectNumber
