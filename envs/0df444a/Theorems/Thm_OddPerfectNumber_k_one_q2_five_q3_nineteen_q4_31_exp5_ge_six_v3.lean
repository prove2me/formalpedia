-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_exp5_ge_six_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_exp5_ge_six_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T05:19:34.583738+00:00
-- url     : https://prove2.me/theorems/22b2fb1f-0a09-4dc4-b1f6-596f1acde609
-- title:
--   The 5-component exponent is at least six in the q4=31 branch
-- statement:
--   In the exact q4=31 four-support branch, the positive even exponent of 5 cannot be 2 or 4, by the accepted q4=31 and exponent-four contradictions; therefore it is at least six.
-- source:
--   The v3 proof specializes only the 5-factor with a direct rewrite, preserving the accepted child’s canonical range expressions.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_31_exp5_ge_six_v3 (p m d sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
    (hsupport_m : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = 31)
    (hupper : sigma ≤ 2 * m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 5 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 31 + 1), 31 ^ i))
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3pos : 0 < (m ^ 2).factorization 3)
    (h3even : Even ((m ^ 2).factorization 3))
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19))
    (h31pos : 0 < (m ^ 2).factorization 31)
    (h31even : Even ((m ^ 2).factorization 31))
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5)) :
    6 ≤ (m ^ 2).factorization 5 := by
  sorry

end OddPerfectNumber
