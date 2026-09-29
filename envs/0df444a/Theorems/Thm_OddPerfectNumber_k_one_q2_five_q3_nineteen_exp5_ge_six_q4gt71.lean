-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt71
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt71
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T22:14:11.481267+00:00
-- url     : https://prove2.me/theorems/dc970200-3a80-421e-b89a-0814ae1fab3c
-- title:
--   The 5-component exponent is at least six when the fourth support prime exceeds 71
-- statement:
--   An even positive exponent below 6 is either 2 or 4. The accepted role theorem rules out exponent 2 under q4>71, and the accepted 5^4 certificate rules out exponent 4.
-- source:
--   Assume the exponent is below 6. Positivity and evenness reduce it to 2 or 4. In the first case apply the accepted 5^2 source-role theorem and eliminate p=31 using the Euler congruence and q4=31 using q4>71. In the second case apply the accepted 5^4 contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd_q4gt71

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt71 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 71 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5even : Even ((m ^ 2).factorization 5))
    (h5pos : 0 < (m ^ 2).factorization 5) :
    6 ≤ (m ^ 2).factorization 5 := by sorry

end OddPerfectNumber
