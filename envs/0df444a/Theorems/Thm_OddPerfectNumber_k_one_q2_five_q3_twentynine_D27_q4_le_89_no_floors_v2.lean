-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_q4_le_89_no_floors_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_q4_le_89_no_floors_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T22:56:47.402656+00:00
-- url     : https://prove2.me/theorems/f90cb814-a22f-4071-bd8e-449bf000e391
-- title:
--   D=27 fourth-prime upper cut without exponent floors
-- statement:
--   Let m,a,b,c,e,D,p,q and sigma be natural numbers. Suppose m squared is 3^(2a)5^(2b)29^(2c)q^(2e), and sigma is the product of the four corresponding geometric sums, including the constant term. Assume D sigma = p m squared, D=27, and p=2D-1 is prime. If q>29 is prime, then q≤89. No lower bounds on the half exponents a,b,c,e are required.
--
--   This upper cut supplies the finite fourth-prime enumeration in the D=27 subcase of the four-support argument.
-- source:
--   Interface weakening of accepted OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_q4_le_89_v1, UUID 1c751ab1-b72a-4bef-a0af-123d86d00c0a: its geometric upper-bound argument uses none of the four numerical exponent floors. Derived finite-branch lemma, not a quotation.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D27_q4_le_89_no_floors_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 27) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 29 < q4) : q4 ≤ 89 := by sorry

end OddPerfectNumber
