-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T08:49:46.827749+00:00
-- url     : https://prove2.me/theorems/53259e1a-5339-4c94-855c-9fa0d160e80c
-- title:
--   q3=29 D27 contradiction, canonical half-floors
-- statement:
--   Weakened interface of D27_absurd_v1.
-- source:
--   Weakened interface; identical proof.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_q4_le_89_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_q4_cases_v1
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_nonexception_absurd_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_q4_53_absurd_v1
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_exception_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D27_absurd_v2 (m d sigma D p q4 a b c e : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 27)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2) (hm0 : m ≠ 0)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) : False := by
  sorry

end OddPerfectNumber
