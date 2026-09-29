-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_half_exp5_one_forces_q4_31_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_half_exp5_one_forces_q4_31_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T15:58:46.59092+00:00
-- url     : https://prove2.me/theorems/5517404f-eff3-4a82-9068-4fd0fc8750ee
-- title:
--   q17 b=1 forces q4=31 via sigma(5^2)=31
-- statement:
--   If the 5-half-exponent is 1 then q4=31, since sigma(5^2)=31 must be p or in support and the p-case is impossible.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_half_exp5_one_forces_q4_31_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 17 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 17 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h17mem : 17 ∈ (m ^ 2).primeFactors)
    (h17exp : (m ^ 2).factorization 17 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 1 ∨ q4 = 31 := by
  sorry

end OddPerfectNumber
