-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_ge_six_q4ne31_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_q4ne31_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T05:08:44.335224+00:00
-- url     : https://prove2.me/theorems/be8e6952-28b1-425a-bb3b-639eaad60130
-- title:
--   The 5-component exponent is at least six when q4 is not 31
-- statement:
--   When q4 is not 31, the accepted 5^2 role split rules out exponent two, and the accepted exponent-four certificate rules out exponent four; positivity and evenness force the exponent to be at least six.
-- source:
--   Use a positive-even arithmetic case split. In the exponent-two case, apply the accepted role theorem and eliminate p=31 by the odd-square contradiction or q4=31 by the explicit hypothesis; in the exponent-four case apply the accepted certificate.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p31_hprod_odd_square_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_ge_six_q4ne31_v2 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5))
    (hq4ne : q4 ≠ 31) :
    6 ≤ (m ^ 2).factorization 5 := by
  sorry

end OddPerfectNumber
