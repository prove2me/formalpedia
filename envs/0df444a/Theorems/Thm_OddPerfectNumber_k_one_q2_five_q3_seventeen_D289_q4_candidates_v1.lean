-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_q4_candidates_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_q4_candidates_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:51:47.031082+00:00
-- url     : https://prove2.me/theorems/93f1c16e-e1a3-400c-a02c-34d9e317452a
-- title:
--   q17 D289 fourth-prime candidates
-- statement:
--   Under q17 canonical factorisation with positive half exponents and D=289 (p=577), q4 is one of 31,61,151,181,211,241,271,331,421.
-- source:
--   Finite q4 enumeration for q17 D289 via canonical abundance window.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D289_q4_candidates_v1 (m a b c e D p q4 sigma : Nat)
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
    (hD : D = 289) :
    q4 = 31 ∨ q4 = 61 ∨ q4 = 151 ∨ q4 = 181 ∨ q4 = 211 ∨ q4 = 241 ∨ q4 = 271 ∨ q4 = 331 ∨ q4 = 421 := by sorry

end OddPerfectNumber
