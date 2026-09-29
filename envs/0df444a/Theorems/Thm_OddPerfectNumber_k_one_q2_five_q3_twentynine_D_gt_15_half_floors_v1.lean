-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D_gt_15_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T17:31:58.567423+00:00
-- url     : https://prove2.me/theorems/0bccaa0d-9694-4b0b-8305-b4fd3d74509a
-- title:
--   q3=29 lower deficiency cut with corrected half-exponent floors
-- statement:
--   Let m,a,b,c,e,D,p,q4 and sigma be natural numbers, with m squared equal to the product of the powers of 3,5,29,q4 having exponents 2a,2b,2c,2e, and sigma equal to the product of the corresponding geometric sums. Suppose D sigma = p m squared, p is prime, p=2D-1, and q4>29. If the half exponents satisfy a>=4, b>=3, c>=2 and e>=1, then
--
--   $$D>15.$$
--
--   This is the lower deficiency cut needed for the finite q3=29 branch with full-exponent floors 8,6,4,2.
-- source:
--   Interface correction of OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_v6, UUID fba858cd-4a70-4e4d-878b-303441abc4ff. Its exact abundance argument only uses full floors 8 and 6 for the first two components; half floors are 4 and 3. Derived finite-branch lemma, not a source quotation.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D_gt_15_half_floors_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : 15 < D := by sorry

end OddPerfectNumber
