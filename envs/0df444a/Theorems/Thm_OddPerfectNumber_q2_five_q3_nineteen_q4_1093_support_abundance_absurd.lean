-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_support_abundance_absurd
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_1093_support_abundance_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T03:15:09.419068+00:00
-- url     : https://prove2.me/theorems/fa68cde3-89b2-4fa9-bfdc-eb5545db5472
-- title:
--   The q4=1093 support role exceeds the half-successor abundance target
-- statement:
--   Under the q4=1093 support factorization, the finite half-successor candidates below 51 are incompatible with the exact abundancy relation and exponent floors.
-- source:
--   Finite abundance certificate for the q4=1093 support-role branch; it uses the accepted half-successor candidate interface and exact cross-multiplied local lower bounds.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_1093_support_abundance_absurd (m b c e D p sigma : Nat)
    (hfac : m ^ 2 = 3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (6 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 1093 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDcases : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45)
    (hp : p = 2 * D - 1)
    (hb : 6 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
