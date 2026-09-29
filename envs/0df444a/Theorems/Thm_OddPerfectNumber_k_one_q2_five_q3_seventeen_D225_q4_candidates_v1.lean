-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D225_q4_candidates_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_q4_candidates_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:51:44.516123+00:00
-- url     : https://prove2.me/theorems/663e6cde-b9cc-4c3b-a6df-0e8df3785d85
-- title:
--   q17 D225 fourth-prime candidates
-- statement:
--   Under q17 canonical factorisation with positive half exponents and D=225 (p=449), q4 is one of 103,137,239,307,409,443.
-- source:
--   Finite q4 enumeration for q17 D225 via canonical abundance window.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D225_q4_candidates_v1 (m a b c e D p q4 sigma : Nat)
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
    (hD : D = 225) :
    q4 = 103 ∨ q4 = 137 ∨ q4 = 239 ∨ q4 = 307 ∨ q4 = 409 ∨ q4 = 443 := by sorry

end OddPerfectNumber
