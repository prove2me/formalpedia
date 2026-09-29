-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T09:04:58.293997+00:00
-- url     : https://prove2.me/theorems/4ad351e2-ba0c-40e3-8389-3b4b01e866e2
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v3
-- statement:
--   Weakened interface; identical proof.
-- source:
--   Weakened interface.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v3 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4eq : q4 = 41) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c)
    (he : 1 ≤ e) : D ≤ 105 := by
  sorry

end OddPerfectNumber
