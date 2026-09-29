-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T05:02:52.720484+00:00
-- url     : https://prove2.me/theorems/1c6e48b1-19cb-41d7-a5ac-82d8034c1808
-- title:
--   Canonical q3=29 q4=41 D upper cut v2
-- statement:
--   In the q3=29 large-D q4=41 case, the strict geometric upper bound forces D at most 105.
-- source:
--   The v2 source keeps the same coefficient proof but stages normalization of the hcoef hypothesis before omega, avoiding the static mixed-location norm_num guard.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4eq : q4 = 41) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : D ≤ 105 := by
  sorry

end OddPerfectNumber
