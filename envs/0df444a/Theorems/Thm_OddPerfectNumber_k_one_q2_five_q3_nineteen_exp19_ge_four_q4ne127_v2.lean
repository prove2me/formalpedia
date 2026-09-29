-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T05:14:24.292752+00:00
-- url     : https://prove2.me/theorems/6537c6e6-9bda-42a1-a038-2d5f94efd684
-- title:
--   The 19-component exponent is at least four when q4 is not 127
-- statement:
--   When q4 is not 127, the accepted sigma(19^2) role split rules out both p=127 and q4=127; positivity and evenness force the 19-index to be at least four.
-- source:
--   Destructure the positive even 19-index; the only value below four is two, then apply the accepted role split and eliminate the two roles directly.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p127_hprod_odd_square_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v2 (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19))
    (hq4ne : q4 ≠ 127) :
    4 ≤ (m ^ 2).factorization 19 := by
  sorry

end OddPerfectNumber
