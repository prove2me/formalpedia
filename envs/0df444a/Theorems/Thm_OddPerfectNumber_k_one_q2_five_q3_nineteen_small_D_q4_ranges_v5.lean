-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_q4_ranges_v5
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_ranges_v5
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T21:58:42.239062+00:00
-- url     : https://prove2.me/theorems/c8e7df9f-c533-432c-96cb-a715c67ca530
-- title:
--   Canonical q3=19 small-D fourth-prime abundance windows v5
-- statement:
--   Under the q3=19 canonical factorization and exponent floors, the D=57,75,135 small-D survivors satisfy their accepted q4 abundance windows.
-- source:
--   Changed replacement with explicit common-factor normalization for the last-three-term lower abundance inequality and concrete D substitutions.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_q4_ranges_v5 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDcases : D = 57 ∨ D = 75 ∨ D = 135) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hDq : D < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : ((D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨ (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨ (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148)) := by
  sorry

end OddPerfectNumber
