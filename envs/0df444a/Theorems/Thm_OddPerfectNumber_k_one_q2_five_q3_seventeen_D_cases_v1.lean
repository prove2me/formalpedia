-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D_cases_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D_cases_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-18T11:35:10.088773+00:00
-- url     : https://prove2.me/theorems/6dd8277c-5936-40af-a29c-fc61a50e1927
-- title:
--   q17 deficient-factor case split
-- statement:
--   Under canonical q17 coordinates, the deficient factor (p+1)/2 is one of 135, 225, 255, 289.
-- source:
--   Finite D-filter for the q17 branch via canonical abundance bounds.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D_cases_v1 (p m d q4 a b c e sigma : Nat)
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
    (p + 1) / 2 = 135 ∨ (p + 1) / 2 = 225 ∨ (p + 1) / 2 = 255 ∨ (p + 1) / 2 = 289 := by sorry

end OddPerfectNumber
