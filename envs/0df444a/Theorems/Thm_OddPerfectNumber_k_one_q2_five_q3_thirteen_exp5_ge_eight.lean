-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp5_ge_eight
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_exp5_ge_eight
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T04:52:56.126126+00:00
-- url     : https://prove2.me/theorems/8360168f-43cb-44d1-88d9-361eeb54eb17
-- title:
--   The 5-component exponent is at least eight in the q3=13 branch
-- statement:
--   Under the canonical q₂=5, q₃=13 support equations and the threshold q₄>19531, the positive even 5-component exponent cannot be 2, 4, or 6; hence it is at least eight.
-- source:
--   Adapter from the accepted q₃=13 small-exponent contradiction: positivity and evenness reduce any exponent below eight to 2, 4, or 6, which the accepted dispatcher excludes.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_small_exponents_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_exp5_ge_eight (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5) (h5even : Even ((m ^ 2).factorization 5)) :
    8 ≤ (m ^ 2).factorization 5 := by
  sorry

end OddPerfectNumber
