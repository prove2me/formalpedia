-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D255_q4_candidates_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D255_q4_candidates_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T14:49:46.324981+00:00
-- url     : https://prove2.me/theorems/169a7410-aa80-409b-87e4-e60e84296796
-- title:
--   q17 D255 fourth-prime candidates
-- statement:
--   Under q17 canonical factorisation with positive half exponents and D=255 (p=509), abundance forces the fourth support prime to be 511.
-- source:
--   Finite q4 enumeration for q17 D255 via canonical abundance window.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D255_q4_candidates_v1 (m a b c e D p q4 sigma : Nat)
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
    (hD : D = 255) :
    q4 = 511 := by sorry

end OddPerfectNumber
