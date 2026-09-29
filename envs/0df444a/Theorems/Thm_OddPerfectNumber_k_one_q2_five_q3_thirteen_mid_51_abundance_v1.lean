-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_mid_51_abundance_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_mid_51_abundance_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:32:56.322983+00:00
-- url     : https://prove2.me/theorems/3f3e80c3-0f05-4a32-9072-3c9d69e51814
-- title:
--   q3=13 middle candidate D=51 dies by abundance
-- statement:
--   The middle-range candidate D=51, p=101, q4=17 is impossible: minimum abundancy at half floors (1,4,1,1) already exceeds 101/51. With S(3,2)/9, S(5,8)/5^8, S(13,2)/169, S(17,2)/289 as cross-multiplied lower bounds, C*sigma >= K*m^2 with C*101 < K*51 contradicts 51*sigma = 101*m^2.
-- source:
--   Canonical q3=13 middle-candidate abundance elimination. EXPONENT CONVENTION: a,b,c,e are HALF exponents. Consumes two accepted sharp ratio bounds; proves the 5- and 17-cases inline by range-splitting plus the identities 4*R+1=5^k and 16*R+1=17^k.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_mid_51_abundance_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 51) (hp_eq : p = 101) (hq4eq : q4 = 17)
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by sorry

end OddPerfectNumber
