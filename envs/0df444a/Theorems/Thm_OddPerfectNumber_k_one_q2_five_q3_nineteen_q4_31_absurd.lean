-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_absurd
-- status  : Open
-- author  : @WillR
-- created : 2026-09-14T01:02:50.934508+00:00
-- url     : https://prove2.me/theorems/fc804ffc-4c9e-49db-b47a-4121e771ca14
-- title:
--   The canonical q4=31 four-support branch is impossible
-- statement:
--   In the canonical k=1 four-support configuration with support {3,5,19,31}, a 5-component of exponent two contradicts the accepted minimum-abundance certificate once the 3-component has exponent at least six.
-- source:
--   Canonical branch wrapper: derive the exponent floors from the accepted 3-component exclusions and invoke the accepted q4=31 variable-exponent abundance contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_four_absurd
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_of_factorization

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_31_absurd (p m d sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : (m ^ 2).primeFactors = {3, 5, 19, 31})
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
