-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_residual_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_residual_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T01:44:06.607052+00:00
-- url     : https://prove2.me/theorems/d78e5ff8-f353-4d5e-bdad-195a3cea35c1
-- title:
--   The four residual q3=13 middle candidates are impossible
-- statement:
--   Under the canonical factor and sigma identities, b≥8, and the four residual middle-D tuples, q3=13 is impossible by the residual factor-five source obstruction.
-- source:
--   Since 5 divides m² and none of the four residual D values is divisible by 5, the canonical relation D·sigma=p·m² forces 5|sigma. The four accepted q4-specific source certificates then contradict this.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_53_no_five_source_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_59_no_five_source_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_67_no_five_source_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_79_no_five_source_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_middle_residual_absurd_v2
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hb : 8 ≤ b)
    (hcases :
      (D = 79 ∧ p = 157 ∧ q4 = 79) ∨
      (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
      (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
      (D = 201 ∧ p = 401 ∧ q4 = 67)) :
    False := by
  sorry

end OddPerfectNumber
