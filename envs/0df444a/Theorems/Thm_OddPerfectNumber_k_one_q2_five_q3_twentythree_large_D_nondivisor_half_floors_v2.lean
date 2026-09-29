-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_nondivisor_half_floors_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_nondivisor_half_floors_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T12:02:36.135539+00:00
-- url     : https://prove2.me/theorems/834f2d19-9ddf-4292-8d8a-5ee4b1a55f16
-- title:
--   q3=23 large-D nondivisor contradiction with full exponent floors 8,6,4,2
-- statement:
--   Let m,a,b,c,e,D,p,q4 and sigma be natural numbers, with m²=3^(2a)5^(2b)23^(2c)q4^(2e), and sigma equal to the product of the four corresponding geometric divisor sums. Suppose D sigma=p m², D≥111, p=2D−1 is prime, q4 is a prime in {53,59,61} not dividing D, and every prime divisor of D belongs to {3,5,23,q4}. If the half exponents satisfy a≥4,b≥3,c≥2,e≥1, then these conditions are inconsistent.
--
--   $$\mathrm{False}.$$
--
--   This is the large-D fourth-prime nondivisor subcase with full exponent floors 8,6,4,2. It does not assert those floors from the original branch hypotheses.
-- source:
--   Canonical-interface repair of the accepted OPN nondivisor theorem a08ee1a6-1c0b-4331-a002-2855ab234903, requested in the four-support mission on 2026-09-17. Retains that proof's factor-support enumeration and upper bound; uses exponent-eight certificate bb0d7da2-c841-4251-b098-f391301053a4 and the same telescoping 23-component bound as accepted lower cut 5ef19c3a-3b64-45b1-bb91-2cb9a2ee76c7. Does not import the parent or the older nondivisor theorem.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_dvd_square_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_factor_support_form_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_D_le_481_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v4

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_nondivisor_half_floors_v2 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2*D-1) (hq4prime : q4.Prime)
    (hqcases : q4 = 53 ∨ q4 = 59 ∨ q4 = 61) (hnot : ¬ q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by sorry

end OddPerfectNumber
