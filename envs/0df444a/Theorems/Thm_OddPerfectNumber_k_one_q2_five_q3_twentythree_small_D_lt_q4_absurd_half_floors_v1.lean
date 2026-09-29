-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_small_D_lt_q4_absurd_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_small_D_lt_q4_absurd_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T13:56:58.948157+00:00
-- url     : https://prove2.me/theorems/f3d48e81-bac9-45b0-9415-9c5377bc178d
-- title:
--   q3=23 small-D contradiction below the fourth prime with corrected half-exponent floors
-- statement:
--   Let m,a,b,c,e,D,p,q4,sigma be natural numbers. Assume m²=3^(2a)5^(2b)23^(2c)q4^(2e), sigma is the product of the four corresponding geometric sums, D sigma=p m², D is odd, D<111, p=2D−1 is prime, q4 is prime with 23<q4 and D<q4, and every prime divisor of D belongs to {3,5,23,q4}. If the half exponents satisfy a≥4,b≥3,c≥2,e≥1, these assumptions are contradictory. The full exponent floors are 8,6,4,2. This is the reduced D<q4 small-D arm, not an unconditional canonical branch theorem.
-- source:
--   Corrected-floor interface replacement for the small-D arm of OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_with_exponent_floors_v1 (ef13f319-4f46-4681-84e7-85336290d517). Pure composition of accepted cut 427ea542-b3e9-4c16-8242-bb75a018b171, D27 terminal 6929e0cd-00c2-423e-b630-22b6018680b1, combined D45/D69 terminal b73f9210-1330-4a1b-89f7-a1cf266d68a3 and D75 terminal 3019739c-e60f-4851-a79c-b720b3777224. Exact statements read back as Proved on 2026-09-17.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_half_floors_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D75_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_small_D_lt_q4_absurd_half_floors_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by sorry

end OddPerfectNumber
