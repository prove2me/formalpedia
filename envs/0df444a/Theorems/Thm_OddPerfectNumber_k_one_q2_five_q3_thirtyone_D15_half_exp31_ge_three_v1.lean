-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_half_exp31_ge_three_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_half_exp31_ge_three_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T15:04:43.521979+00:00
-- url     : https://prove2.me/theorems/e49ce543-0ae2-48fb-a231-ea773bbf42cf
-- title:
--   q31 D15 31-half exponent at least three
-- statement:
--   In the q31 D15 branch with q4 != 331, the 31-half exponent is at least 3, from the ne_one/ne_two exclusions.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_D15_half_exp31_ge_three_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hp29 : p = 29)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 31 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4) (hq4ne : q4 ≠ 331)
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
    3 ≤ c := by
  sorry

end OddPerfectNumber
