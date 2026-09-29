-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_q4_31_D_le_106_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_q4_31_D_le_106_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T06:01:46.43042+00:00
-- url     : https://prove2.me/theorems/9f7ec03e-fe3f-4c6f-bdb9-adc8a3e28137
-- title:
--   q3=29 b=1 q4=31 D upper bound
-- statement:
--   With b=1 and q4=31, exact 31/25 plus strict geometric upper bounds force D<107.
-- source:
--   Clone of the accepted q4=41 D_le_105 coefficient proof, with exact S(5,2)=31 replacing the 5-upper bound.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_b_one_q4_31_D_le_106_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4eq : q4 = 31)
    (hb1 : b = 1) (ha : 4 ≤ a) (hc : 2 ≤ c) (he : 1 ≤ e) :
    D < 107 := by
  sorry

end OddPerfectNumber
