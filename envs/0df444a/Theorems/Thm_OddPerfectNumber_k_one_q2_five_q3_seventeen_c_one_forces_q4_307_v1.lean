-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_c_one_forces_q4_307_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_c_one_forces_q4_307_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T15:26:38.94663+00:00
-- url     : https://prove2.me/theorems/d8f120b1-8ef3-4999-bc05-c0d6756b80b6
-- title:
--   q17 c=1 forces q4=307 via sigma(17^2)=307
-- statement:
--   In the canonical q2=5,q3=17 branch, 17-half-exponent 1 forces the fourth prime to be 307.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_c_one_forces_q4_307_v1 (p m d q4 a b c e sigma : Nat)
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
    c ≠ 1 ∨ q4 = 307 := by
  sorry

end OddPerfectNumber
