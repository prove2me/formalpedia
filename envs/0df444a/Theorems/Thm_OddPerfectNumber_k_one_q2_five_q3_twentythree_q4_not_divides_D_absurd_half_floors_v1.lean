-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T14:18:18.386178+00:00
-- url     : https://prove2.me/theorems/a86b8924-90e5-4ea4-a503-854c02573dff
-- title:
--   Small-D fourth-prime nondivisor contradiction with corrected half floors
-- statement:
--   Let m,a,b,c,e,D,p,q4 and sigma be natural numbers, with m²=3^(2a)5^(2b)23^(2c)q4^(2e), and sigma the corresponding geometric divisor-sum product. Suppose D sigma=p m², D is odd and less than 111, p=2D−1 is prime, and q4 is prime with 23<q4≤D. Suppose q4 does not divide D and every prime divisor of D is in {3,5,23,q4}. If the half exponents satisfy a≥4,b≥3,c≥2,e≥1, these assumptions are contradictory.
--
--   This eliminates the small-D nondivisor arm using full exponent floors 8,6,4,2; it does not assert complete canonical branch coverage.
-- source:
--   Source-faithful interface repair of the existing OPN small-D nondivisor arm, using accepted finite reduction 30e96d4d-37d8-43f9-b13b-8792e7f03c17 and corrected full exponent floors 8,6,4,2 from the user-supplied four-support plan. Exact abundance coefficient margin: 75*4161135550728494−149*2094229476140625=44974359683925>0. New independent replacement, no mutation or dependency on the overstrong terminal.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_half_floors_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hq4notdiv : ¬ q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (hq4le : q4 ≤ D) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c)
    (he : 1 ≤ e) : False := by sorry

end OddPerfectNumber
