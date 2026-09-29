-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T11:21:58.568302+00:00
-- url     : https://prove2.me/theorems/5ef19c3a-3b64-45b1-bb91-2cb9a2ee76c7
-- title:
--   D=27 fourth-prime lower cut with full exponent floors 8,6,4,2
-- statement:
--   Let m,a,b,c,e,D,p,q4 and sigma be natural numbers with m²=3^(2a)5^(2b)23^(2c)q4^(2e), and let sigma be the corresponding product of geometric sums. Suppose D sigma=p m², D=27, p=2D−1, and q4 is prime and exceeds 23. Assume the half-exponent bounds a≥4, b≥3, c≥2, e≥1. Then
--
--   $$q_4\ge691.$$
--
--   This is a lower-cut reduction for the D=27 subcase; it does not assume or establish a complete four-support branch contradiction.
-- source:
--   OPN four-support interface correction, 2026-09-17: weaker-premise replacement of theorem 7a98cc4f-7276-4ca0-b452-92e983435777. Explicit half exponent convention; exact geometric abundance inequality at full exponents 8,6,4,2, followed by primality exclusion of 684 through 690.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 27) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : 691 ≤ q4 := by sorry

end OddPerfectNumber
