-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D135_q4_candidates_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D135_q4_candidates_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:43:44.420353+00:00
-- url     : https://prove2.me/theorems/3b0d4522-26bc-477e-808a-e28b1658489f
-- title:
--   q17 D135 fourth-prime candidates
-- statement:
--   Under q17 canonical factorisation with positive half exponents and D=135 (p=269), the fourth support prime is one of 1021, 1531, 2551, 3061, 3571, 4591.
-- source:
--   Finite q4 enumeration for q17 D135 via canonical abundance window (q4 = 1 mod 255, q4 <= 4918).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D135_q4_candidates_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hq4 : q4.Prime) (hq4gt : 17 < q4)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hD : D = 135) :
    q4 = 1021 ∨ q4 = 1531 ∨ q4 = 2551 ∨ q4 = 3061 ∨ q4 = 3571 ∨ q4 = 4591 := by sorry

end OddPerfectNumber
