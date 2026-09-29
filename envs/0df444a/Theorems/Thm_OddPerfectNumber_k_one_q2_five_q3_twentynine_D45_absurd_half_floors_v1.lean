-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_absurd_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_absurd_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T17:46:27.055488+00:00
-- url     : https://prove2.me/theorems/73509cd8-5b70-4629-a49c-06c20aefdba5
-- title:
--   q3=29 D=45 contradiction with corrected half-exponent floors
-- statement:
--   Let m,a,b,c,e,D,p,q4 and sigma be natural numbers. Suppose m squared is the product of the powers of 3,5,29,q4 with full exponents 2a,2b,2c,2e, and sigma is the corresponding product of geometric sums. Assume D sigma = p m squared, D=45, p=2D-1, and q4 is prime and exceeds 29. The half-exponent bounds a>=4,b>=3,c>=2,e>=1 are then incompatible with these equations.
--
--   There is no such D=45 configuration.
--
--   This is the D=45 terminal subcase for the q3=29 finite branch, using full-exponent floors 8,6,4,2. It does not itself derive those floors.
-- source:
--   Corrected half-exponent interface of OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_canonical_absurd_v2, UUID a43c0330-adf5-47c7-abf9-a38809eefbef. Retains its exact abundance proof and constants; derived OPN finite-branch lemma, not a source quotation.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D45_absurd_half_floors_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 45) (hp_eq : p = 2 * D - 1) (hq4 : q4.Prime) (hq4gt : 29 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by sorry

end OddPerfectNumber
