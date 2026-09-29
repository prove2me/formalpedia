-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_two_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:18:12.206171+00:00
-- url     : https://prove2.me/theorems/de9f3c18-5440-49d1-a1e9-30114cb7bc7e
-- title:
--   The b=2 q2=5 q3=19 branch is impossible
-- statement:
--   The accepted role split reduces b=2 to p=31 or q4=31; the former is impossible for an odd square half-successor and the latter is closed by the accepted q4=31 branch theorem.
-- source:
--   Small dispatcher composing only accepted role and branch contradictions.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_p31_hprod_odd_square_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_absurd_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_two_absurd_v2 (p m d sigma q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
    (hsupport_m : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2)
    (hupper : sigma ≤ 2 * m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 31 + 1), 31 ^ i))
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3pos : 0 < (m ^ 2).factorization 3)
    (h3even : Even ((m ^ 2).factorization 3))
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19))
    (h31pos : 0 < (m ^ 2).factorization 31)
    (h31even : Even ((m ^ 2).factorization 31)) :
    False := by
  sorry

end OddPerfectNumber
