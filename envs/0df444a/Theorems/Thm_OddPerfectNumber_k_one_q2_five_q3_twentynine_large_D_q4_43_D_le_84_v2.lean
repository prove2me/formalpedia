-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_43_D_le_84_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_43_D_le_84_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T09:07:41.889271+00:00
-- url     : https://prove2.me/theorems/f0c46c63-455b-4f60-a9f8-11e2db2f9d5b
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_43_D_le_84_v2
-- statement:
--   Weakened interface; identical proof.
-- source:
--   Weakened interface.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_43_D_le_84_v2 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4eq : q4 = 43) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c)
    (he : 1 ≤ e) : D ≤ 84 := by
  sorry

end OddPerfectNumber
