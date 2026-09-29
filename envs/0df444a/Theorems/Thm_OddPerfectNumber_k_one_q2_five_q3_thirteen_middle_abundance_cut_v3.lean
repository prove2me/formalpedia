-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:06:28.170673+00:00
-- url     : https://prove2.me/theorems/0c05869a-80d6-4b5c-865e-c6306e4877fa
-- title:
--   Nine low-q4 q3=13 middle candidates are impossible (half floors)
-- statement:
--   Under the canonical factor and sigma identities, half-exponent floors a>=1,b>=4,c>=1,e>=1, and the nine-case low-q4 disjunction, q3=13 is impossible by the accepted per-candidate abundance and support kills.
-- source:
--   Weakened half-floor dispatch replacing middle_abundance_cut_v2; consumes nine Proved per-candidate kills.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_51_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_57_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_69_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_87_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_115_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_129_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_141_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_205_abundance_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_187_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_middle_abundance_cut_v3 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hm : Odd m)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hDm : D ∣ m ^ 2)
    (hcases :
      (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
      (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
      (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
      (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
      (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
      (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
      (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
      (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
      (D = 205 ∧ p = 409 ∧ q4 = 41))
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
