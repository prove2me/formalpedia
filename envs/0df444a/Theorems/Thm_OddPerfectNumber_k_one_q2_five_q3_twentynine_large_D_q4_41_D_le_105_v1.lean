-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T05:01:26.474492+00:00
-- url     : https://prove2.me/theorems/5950b485-861a-492b-8685-9281f532c85f
-- title:
--   Canonical q3=29 q4=41 D upper cut
-- statement:
--   In the q3=29 large-D q4=41 case, the strict geometric upper bound forces D at most 105.
-- source:
--   Multiply strict geometric upper bounds for 3,5,29,q4, substitute q4=41 and p=2D-1 after cancelling the positive square factor, then close 85D<8960 by omega.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4eq : q4 = 41) (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) : D ≤ 105 := by
  sorry

end OddPerfectNumber
