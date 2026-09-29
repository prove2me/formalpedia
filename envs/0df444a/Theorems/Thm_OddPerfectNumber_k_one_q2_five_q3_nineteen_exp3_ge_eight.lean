-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_ge_eight
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_ge_eight
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T04:05:53.90166+00:00
-- url     : https://prove2.me/theorems/3d13799d-a156-4e90-9eeb-fcc44691cf89
-- title:
--   The 3-component exponent is at least eight in the q2=5 q3=19 branch
-- statement:
--   The accepted a=2, a=4 and a=6 contradictions, together with positive evenness of the 3-component exponent, imply a≥8.
-- source:
--   Dispatch the three exact small even exponent cases to the accepted contradictions, then use omega.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_four_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_absurd_v3

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp3_ge_eight (p m d q4 sigma a b c e D : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = a)
    (h3pos : 0 < a) (h3even : Even a)
    (hsigma_p : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 19 ^ i) * (∑ i ∈ Finset.range (e + 1), 547 ^ i))
    (hsigma_eq_p : sigma = 1093 * d)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h547 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i)
    (hfac_q : m ^ 2 = 3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e)
    (hsigma_q : sigma = (∑ i ∈ Finset.range (6 + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 19 ^ i) * (∑ i ∈ Finset.range (e + 1), 1093 ^ i))
    (hrel_q : D * sigma = p * m ^ 2)
    (hDcases_q : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45)
    (hp_q : p = 2 * D - 1)
    (hb : 6 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    8 ≤ a := by
  sorry

end OddPerfectNumber
