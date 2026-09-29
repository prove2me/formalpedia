-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_q4_le_89_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_q4_le_89_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T08:46:58.671921+00:00
-- url     : https://prove2.me/theorems/cd0bcc9d-7152-409d-a594-07dd0e8d0a56
-- title:
--   q3=29 D27 q4<=89, canonical half-floors
-- statement:
--   Weakened interface of D27_q4_le_89_v1.
-- source:
--   Weakened interface; identical proof.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D27_q4_le_89_v2 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    q4 ≤ 89 := by
  sorry

end OddPerfectNumber
