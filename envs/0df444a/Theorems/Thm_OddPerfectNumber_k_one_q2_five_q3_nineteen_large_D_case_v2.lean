-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_case_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_case_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T20:48:47.897391+00:00
-- url     : https://prove2.me/theorems/b023375d-cfb2-4c1c-9c5f-453161d9bb5f
-- title:
--   Canonical q3=19 large-D tuple reduction
-- statement:
--   Under the canonical q3=19 large-D hypotheses, the six q4 cases and exact abundance windows feed the accepted finite factor-support enumeration, forcing D=855, q4=101, and p=1709.
-- source:
--   Compose the canonical six-way q4 reduction, the six exact abundance windows, and the accepted finite factor-support tuple theorem.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_factor_support_form_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_six_cases
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_97_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_103_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_107_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_109_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_113_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_tuple_from_factor_support

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_large_D_case_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 225 ≤ D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) : D = 855 ∧ q4 = 101 ∧ p = 1709 := by
  sorry

end OddPerfectNumber
