-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_le_61_no_floors_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_le_61_no_floors_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T12:08:50.250138+00:00
-- url     : https://prove2.me/theorems/6bd9598b-e03d-4dcf-b96f-651756f15c88
-- title:
--   q3=23 large-D fourth-prime upper bound without exponent floors
-- statement:
--   Let m,a,b,c,e,D,p,q4,sigma be natural numbers. Suppose m²=3^(2a)5^(2b)23^(2c)q4^(2e), sigma equals the product of the four corresponding geometric sums, D sigma=p m², D≥111, p=2D−1 is prime, and q4>23 is prime. Then
--
--   $$q_4\le61.$$
--
--   No lower bounds on the half exponents a,b,c,e are required. This is the canonical large-D upper cut, not a complete branch contradiction.
-- source:
--   Unused-premise removal from accepted OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_le_61_v2, UUID 5f928a16-0a57-4c9d-bbc8-dbad3fb7e7cf. Its source proof uses only strict geometric upper bounds, the displayed product identity, D>=111 and primality. Canonical-interface audit requested 2026-09-17; no import of the older theorem or parent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_q4_le_61_no_floors_v3 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) : q4 ≤ 61 := by sorry

end OddPerfectNumber
