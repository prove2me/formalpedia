-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ge_four_smallq4_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ge_four_smallq4_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T10:21:54.958081+00:00
-- url     : https://prove2.me/theorems/6a6e0881-832a-442d-994b-275381d29c7d
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ge_four_smallq4_v1
-- statement:
--   q13 half-exponent b>=4 under range-local q4<=89, composing b!=1, b!=2, b!=3.
-- source:
--   q13 floor program (range-local composition).

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ne_one_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ne_two_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ne_three_smallq4_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_half_exp5_ge_four_smallq4_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4) (hq4le : q4 ≤ 89)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h13mem : 13 ∈ (m ^ 2).primeFactors)
    (h13exp : (m ^ 2).factorization 13 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    4 ≤ b := by
  sorry

end OddPerfectNumber
