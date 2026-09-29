-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_31_abundance_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_31_abundance_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T22:59:13.078097+00:00
-- url     : https://prove2.me/theorems/5e397f96-414d-45a7-846d-943548d7f9c1
-- title:
--   q3=29 D=45 q4=31 abundance contradiction
-- statement:
--   The q3=29 D=45 q4=31 subcase exceeds the exact abundance ratio using the accepted exponent floors.
-- source:
--   Multiply the accepted lower geometric-sum ratio bounds for bases 3, 5 and 31 with the last-two-term bound for base 29; the resulting exact integer lower bound is incompatible with 45 sigma = 89 m^2.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirtyone_ge_two
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D45_q4_31_abundance_absurd (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 45) (hp_eq : p = 2 * D - 1) (hq4 : q4 = 31)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
