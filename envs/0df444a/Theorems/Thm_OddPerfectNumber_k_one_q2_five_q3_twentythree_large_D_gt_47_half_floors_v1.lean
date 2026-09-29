-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T12:35:41.278983+00:00
-- url     : https://prove2.me/theorems/f861b6fb-9e3c-44c5-8ef5-a7d9dcdd9930
-- title:
--   Fourth prime exceeds 47 under full exponent floors 8,6,4,2
-- statement:
--   Let m,a,b,c,e,D,p,q4 and sigma be natural numbers with m²=3^(2a)5^(2b)23^(2c)q4^(2e), and let sigma be the corresponding product of geometric divisor sums. Suppose D>0, D sigma=p m², p=2D−1, and q4 is prime and exceeds 23. If the half exponents satisfy a≥4,b≥3,c≥2,e≥1, then
--
--   $$q_4>47.$$
--
--   This is a fourth-prime lower cut for the q3=23 branch with full exponent floors 8,6,4,2. It does not derive those floors from the original Euler hypotheses or assert an all-D contradiction.
-- source:
--   OPN four-support canonical-interface repair requested 2026-09-17: replace excess half-exponent floors in lower-cut ebea6493-8390-433b-bba2-a40fb2ad562f. Uses the same exact lower ratios as accepted corrected D27 cut 5ef19c3a-3b64-45b1-bb91-2cb9a2ee76c7. Exact integer comparison: 2699114951823888 > 2*1348339525734375. D>0 excludes the degenerate D=p=0 relation.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDpos : 0 < D) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : 47 < q4 := by sorry

end OddPerfectNumber
