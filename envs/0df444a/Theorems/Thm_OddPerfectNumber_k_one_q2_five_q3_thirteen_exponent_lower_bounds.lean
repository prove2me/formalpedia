-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exponent_lower_bounds
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_exponent_lower_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T17:06:42.738231+00:00
-- url     : https://prove2.me/theorems/d7def1e5-d7e4-43da-b01f-02a48391053f
-- title:
--   The q3=13 branch has a=2 and 5-exponent at least eight
-- statement:
--   Under the accepted q2=5, q3=13 canonical hypotheses and q4>19531 threshold, the 3-exponent is exactly two and the 5-exponent in m^2 is at least eight.
-- source:
--   Standalone composition of the accepted a=2 and b>=8 children.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp3_eq_two_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp5_ge_eight

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_exponent_lower_bounds (m a b c e p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 13 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19531 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5))
    (ha2 : 2 ≤ a) (haeven : Even a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    a = 2 ∧ 8 ≤ (m ^ 2).factorization 5 := by
  sorry

end OddPerfectNumber
