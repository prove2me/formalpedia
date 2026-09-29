-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_ge_six_unconditional
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T05:34:07.955206+00:00
-- url     : https://prove2.me/theorems/5de40593-8378-4449-9f53-dc3a832b1246
-- title:
--   The 5-component exponent is at least six in the full q2=5 q3=19 branch
-- statement:
--   In the canonical q2=5, q3=19 four-support branch, the positive even exponent of the 5-component is at least six.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_exp5_ge_six_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_ge_six_q4ne31_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_ge_six_unconditional (p m d q4 sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, q4})
    (hsupport_m : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5))
    (hupper : sigma ≤ 2 * m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 5 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization 19 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range ((m ^ 2).factorization q4 + 1), q4 ^ i)) :
    6 ≤ (m ^ 2).factorization 5 := by
  sorry

end OddPerfectNumber
