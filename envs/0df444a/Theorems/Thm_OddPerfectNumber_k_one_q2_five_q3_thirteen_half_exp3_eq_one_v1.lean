-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_half_exp3_eq_one_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp3_eq_one_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T09:51:38.205113+00:00
-- url     : https://prove2.me/theorems/4e455d9a-fc78-4e5a-ae44-2e9742d64b93
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_thirteen_half_exp3_eq_one_v1
-- statement:
--   q13 half-exponent a=1 via full-exponent exp3_eq_two at doubled variables.
-- source:
--   q13 floor program.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp3_eq_two_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_half_exp3_eq_one_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a = 1 := by
  sorry

end OddPerfectNumber
