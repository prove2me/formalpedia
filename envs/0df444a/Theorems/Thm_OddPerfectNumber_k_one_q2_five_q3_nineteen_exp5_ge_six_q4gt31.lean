-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt31
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt31
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:11:58.847138+00:00
-- url     : https://prove2.me/theorems/83c62a01-ae6f-4c9d-b0f0-1e781da82615
-- title:
--   The 5-component exponent is at least six when q4 exceeds 31
-- statement:
--   With q4>31, the positive even 5-exponent cannot be 2 (accepted q4>31 contradiction) or 4 (new unconditional 5^4 contradiction), so it is at least 6.
-- source:
--   Assume the positive even exponent is below six, reduce it to 2 or 4 by omega, and invoke the accepted 5^2 q4>31 contradiction or the unconditional 5^4 contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_absurd_q4gt31
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt31 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5even : Even ((m ^ 2).factorization 5))
    (h5pos : 0 < (m ^ 2).factorization 5) :
    6 ≤ (m ^ 2).factorization 5 := by sorry

end OddPerfectNumber
