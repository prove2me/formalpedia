-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_absurd_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_absurd_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T11:35:06.640437+00:00
-- url     : https://prove2.me/theorems/6929e0cd-00c2-423e-b630-22b6018680b1
-- title:
--   D=27 contradiction with full exponent floors 8,6,4,2
-- statement:
--   There are no natural numbers m,a,b,c,e,D,p,q4 and sigma satisfying m²=3^(2a)5^(2b)23^(2c)q4^(2e), the corresponding geometric-sum product identity for sigma, and D sigma=p m², with D=27 and p=2D−1, when q4 is prime and exceeds 23 and the half exponents satisfy a≥4, b≥3, c≥2, e≥1.
--
--   $$D=27\quad\Longrightarrow\quad\mathrm{False}.$$
--
--   This is the D=27 subcase contradiction with full exponent floors 8,6,4,2, not an unconditional all-D branch theorem.
-- source:
--   Composition in the OPN four-support proof graph, 2026-09-17. Weaker-floor lower-cut theorem 5ef19c3a-3b64-45b1-bb91-2cb9a2ee76c7; upper cut e4ab7349-da37-4ff5-999c-3addc63eb524; prime window 1e2b9324-faab-4b2d-b4a3-029372cfa9d2; sigma divisibility 5d0f974f-223a-4504-8f73-4eccc503cff1; source obstruction 47a29740-bfb7-4bbe-9877-3fbd65635a94.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_le_717
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_window_cases
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_sigma_div_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_small_D_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D27_absurd_half_floors_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 27) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by sorry

end OddPerfectNumber
