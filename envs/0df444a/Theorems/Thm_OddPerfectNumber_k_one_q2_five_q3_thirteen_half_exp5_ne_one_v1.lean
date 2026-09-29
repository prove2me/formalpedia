-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp5_ne_one_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp5_ne_one_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T08:16:27.155166+00:00
-- url     : https://prove2.me/theorems/c9b7a54a-b35e-4260-b4de-1fc3f688c8fa
-- title:
--   q3=13 half-exponent b is not one
-- statement:
--   In the q2=5,q3=13 branch the half-exponent of 5 is not 1.
-- source:
--   sigma(5^2)=31 support closure: 31=p gives even D=16, 31=q4 dies by minimum abundance.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_half_exp5_ne_one_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hm : Odd m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    b ≠ 1 := by
  sorry

end OddPerfectNumber
