-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_two_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T03:44:24.677275+00:00
-- url     : https://prove2.me/theorems/a83560d4-ef09-4f76-a713-b9993a21149a
-- title:
--   The exponent-two 19-component branch is impossible
-- statement:
--   The accepted sigma(19^2) role split gives p=127 or q4=127; both cases are contradicted by the accepted odd-square and q4=127 source dispatchers.
-- source:
--   Compose the accepted 19^2 role split with the accepted p=127 odd-square contradiction and the q4=127 source dispatcher.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p127_hprod_odd_square_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_q4_127_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp19_two_absurd (p m d q4 sigma a b c e : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsigma_eq : sigma = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hsigma : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 19 ^ i) * (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (hq4 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), q4 ^ i) :
    False := by
  sorry

end OddPerfectNumber
