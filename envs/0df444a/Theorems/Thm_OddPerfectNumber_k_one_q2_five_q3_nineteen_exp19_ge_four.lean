-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_ge_four
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_ge_four
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T04:08:16.789779+00:00
-- url     : https://prove2.me/theorems/920af903-8297-44cc-a5bf-25e4c3c3c600
-- title:
--   The 19-component exponent is at least four in the q2=5 q3=19 branch
-- statement:
--   Positive evenness and the accepted c=2 contradiction imply that the actual 19-component exponent is at least four.
-- source:
--   Assume c<4, use positive evenness to reduce to c=2, then invoke the accepted unconditional c=2 dispatcher.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp19_ge_four (p m d q4 sigma a b c e : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsigma_eq : sigma = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = c)
    (h19pos : 0 < c) (h19even : Even c)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hsigma : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 19 ^ i) * (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (hq4 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), q4 ^ i) :
    4 ≤ c := by
  sorry

end OddPerfectNumber
