-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_31_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_31_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T01:16:20.352181+00:00
-- url     : https://prove2.me/theorems/227c298a-c3d0-4b18-b9d3-aa7f5c89af00
-- title:
--   The corrected canonical q4=31 four-support branch is impossible
-- statement:
--   With the exact canonical support {3,5,19,31} and the 5-component exponent fixed at two, the accepted exponent and abundance certificates rule out the branch.
-- source:
--   Corrected branch wrapper with the exact 5-exponent and factorization-expansion dependencies exposed in the theorem interface.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_four_absurd
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_of_factorization
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_31_absurd_v2 (p m d sigma : Nat)
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
    (h31even : Even ((m ^ 2).factorization 31))
    (h5exp : (m ^ 2).factorization 5 = 2) :
    False := by
  sorry

end OddPerfectNumber
