-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T01:53:40.265978+00:00
-- url     : https://prove2.me/theorems/e471317b-d9f5-4374-9260-3a4bfa3f31bf
-- title:
--   The q3=13 middle-D candidate list is impossible
-- statement:
--   The exact thirteen q3=13 middle candidates are all impossible: nine violate abundance and the remaining four violate the residual factor-five source obstruction.
-- source:
--   Pure dispatch to the accepted nine-case abundance cut and accepted four-case residual source contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_abundance_cut_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_residual_absurd_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_middle_D_absurd_v2
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcases :
      (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
      (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
      (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
      (D = 79 ∧ p = 157 ∧ q4 = 79) ∨
      (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
      (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
      (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
      (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
      (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
      (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
      (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
      (D = 201 ∧ p = 401 ∧ q4 = 67) ∨
      (D = 205 ∧ p = 409 ∧ q4 = 41))
    (hq4prime : q4.Prime) (ha : 2 ≤ a) (hb : 8 ≤ b)
    (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
