-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_129_abundance_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_129_abundance_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:53:33.327973+00:00
-- url     : https://prove2.me/theorems/e323844d-0a66-46a8-8ae2-bd8d73730a59
-- title:
--   q3=13 middle candidate D=129 dies by abundance
-- statement:
--   The middle-range candidate D=129, p=257, q4=43 is impossible: minimum abundancy at half floors (1,4,1,1) already exceeds 257/129.
-- source:
--   Canonical q3=13 middle-candidate abundance elimination. EXPONENT CONVENTION: a,b,c,e are HALF exponents.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_mid_129_abundance_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 129) (hp_eq : p = 257) (hq4eq : q4 = 43)
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by sorry

end OddPerfectNumber
