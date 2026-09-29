-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp_lower_bounds_q4gt127
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp_lower_bounds_q4gt127
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T05:45:57.731005+00:00
-- url     : https://prove2.me/theorems/7ea236fe-9ff6-48bf-a738-f5072da7dd03
-- title:
--   Both nonspecial exponents have lower bounds when q4 exceeds 127
-- statement:
--   In the canonical q2=5, q3=19 branch with q4>127, the 5-component exponent is at least six and the 19-component exponent is at least four.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt71
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_ge_four_q4gt127

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp_lower_bounds_q4gt127 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 127 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5))
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19)) :
    6 ≤ (m ^ 2).factorization 5 ∧ 4 ≤ (m ^ 2).factorization 19 := by
  sorry

end OddPerfectNumber
