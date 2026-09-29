-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_half_exp3_ne_four_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp3_ne_four_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T13:41:34.24758+00:00
-- url     : https://prove2.me/theorems/6a3c1451-7c74-4438-8284-347d5250e451
-- title:
--   q31 D15 3-half-exp != 4
-- statement:
--   With p=29, half-exponent a=4 gives sigma(3^8)=9841=13*757 with 13 prime outside support {3,5,31,q4} (q4>31) and != p.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_D15_half_exp3_ne_four_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hp29 : p = 29)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 31 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 31 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 31 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h31mem : 31 ∈ (m ^ 2).primeFactors)
    (h31exp : (m ^ 2).factorization 31 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≠ 4 := by
  sorry

end OddPerfectNumber
