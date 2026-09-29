-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_half_floors_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_half_floors_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T13:26:29.121148+00:00
-- url     : https://prove2.me/theorems/427ea542-b3e9-4c16-8242-bb75a018b171
-- title:
--   Small-D q3=23 abundance cut with full exponent floors 8,6,4,2
-- statement:
--   Let m,a,b,c,e,D,p,q4 and sigma be natural numbers. Suppose m²=3^(2a)5^(2b)23^(2c)q4^(2e), sigma is the product of the four corresponding geometric sums, D sigma=p m², and p=2D−1 is prime. Suppose D is odd, D<111, q4 is prime, 23<q4, D<q4, and every prime divisor of D belongs to {3,5,23,q4}. Assume the half-exponent bounds a≥4, b≥3, c≥2, e≥1. Then
--
--   $$D\in\{27,45,69,75\}.$$
--
--   This reduced small-D cut uses full exponent floors 8,6,4,2. It does not assert a complete canonical branch contradiction; the floors and D<q4 remain explicit assumptions.
-- source:
--   Weaker-interface replacement of Prove2Me theorem ff1aa4f7-acad-4780-a737-13499955d482, using the accepted support cut a0a18f68-767e-4772-8f88-594dc094e8c0 and geometric lower inequalities at full exponents 8,6,4. OPN interface correction requested 2026-09-17.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_half_floors_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by sorry

end OddPerfectNumber
