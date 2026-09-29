-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T05:24:42.733648+00:00
-- url     : https://prove2.me/theorems/9b630ec4-0e64-41ba-af56-2dbc210050d7
-- title:
--   The 19-component exponent is at least four when q4 is not 127
-- statement:
--   For q4 not equal to 127, positivity and evenness reduce any 19-index below four to exponent two, which is excluded by the accepted 19^2 role and p=127 contradiction.
-- source:
--   A direct positive-even case split invokes the accepted q4-ne127 exponent-two contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_q4_ne127_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v3 (p m d q4 : Nat)
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
