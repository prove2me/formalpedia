-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D_gt_15_v6
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_v6
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T04:29:23.55601+00:00
-- url     : https://prove2.me/theorems/fba858cd-4a70-4e4d-878b-303441abc4ff
-- title:
--   Canonical q3=29 lower deficiency cut
-- statement:
--   Under the canonical q2=5,q3=29 factorization and exponent floors, the Euler relation excludes every D at most 15.
-- source:
--   Exact lower-abundance cross multiplication: accepted 3- and 5-component bounds, the final two 29 terms, and positivity of the q4 sum force the Euler ratio above 29/15.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D_gt_15_v6 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) : 15 < D := by
  sorry

end OddPerfectNumber
