-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T13:34:44.370337+00:00
-- url     : https://prove2.me/theorems/b73f9210-1330-4a1b-89f7-a1cf266d68a3
-- title:
--   Exclude D=45 and D=69 with full exponent floors 8,6,4,2
-- statement:
--   Let m,a,b,c,e,D,p,q4,sigma be natural numbers satisfying m²=3^(2a)5^(2b)23^(2c)q4^(2e), with sigma the product of the corresponding geometric sums. Assume D sigma=p m², p=2D−1, q4 prime, D<q4, and half-exponent floors a≥4,b≥3,c≥2,e≥1. Then
--
--   $$D\notin\{45,69\}.$$
--
--   This excludes two small-D subcases with full exponent floors 8,6,4,2; it is not a complete canonical branch theorem.
-- source:
--   OPN weaker-floor interface repair, 2026-09-17. Combines the accepted upper-bound argument of 3848f237-f84b-4579-955f-8c8db63d4771 with lower ratios at full exponents 8,6,4 and the last two fourth-component terms. Replaces the overstrong floor interfaces of the D45/D69 abundance children.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDcases : D = 45 ∨ D = 69) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hDq : D < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by sorry

end OddPerfectNumber
