-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_115_abundance_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_115_abundance_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:51:07.961966+00:00
-- url     : https://prove2.me/theorems/101dd00e-2576-49d0-8f47-1358ae3290b7
-- title:
--   q3=13 middle candidate D=115 dies by abundance
-- statement:
--   The middle-range candidate D=115, p=229, q4=23 is impossible: minimum abundancy at half floors (1,4,1,1) already exceeds 229/115.
-- source:
--   Canonical q3=13 middle-candidate abundance elimination. EXPONENT CONVENTION: a,b,c,e are HALF exponents.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_mid_115_abundance_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 115) (hp_eq : p = 229) (hq4eq : q4 = 23)
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by sorry

end OddPerfectNumber
