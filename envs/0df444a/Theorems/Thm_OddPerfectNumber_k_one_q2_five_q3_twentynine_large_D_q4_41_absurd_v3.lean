-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T09:20:17.009936+00:00
-- url     : https://prove2.me/theorems/2d8011b1-4b28-4a58-99b8-fe22b90667c2
-- title:
--   Canonical q3=29 q4=41 large-D contradiction v3
-- statement:
--   The q3=29 q4=41 large-D window is contradicted by the sharpened three-final-term abundance bound.
-- source:
--   A changed abundance route uses the last three terms for both the 29 and 41 components, which is strong enough for both surviving D values.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v3 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D) (hDupper : D ≤ 105) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4eq : q4 = 41) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : False := by
  sorry

end OddPerfectNumber
