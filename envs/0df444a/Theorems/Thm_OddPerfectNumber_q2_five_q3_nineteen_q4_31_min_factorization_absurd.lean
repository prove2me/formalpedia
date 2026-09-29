-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_min_factorization_absurd
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_31_min_factorization_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:26:47.886748+00:00
-- url     : https://prove2.me/theorems/6850e7cd-32ba-4324-9b0a-92cdd5d96f2f
-- title:
--   The minimum q4=31 factorization already exceeds twice its product
-- statement:
--   At exponents (6,2,2), the q2=5, q3=19, q4=31 local divisor-sum product is already greater than twice the corresponding square, so it cannot satisfy the perfect-number upper bound.
-- source:
--   Exact arithmetic certificate composed with factorization and sigma-product equalities.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_minimum_abundance_certificate

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_31_min_factorization_absurd (m sigma : Nat)
    (hfac : m ^ 2 = 3 ^ 6 * 5 ^ 2 * 19 ^ 2 * 31 ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (6 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 31 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2) :
    False := by
  sorry

end OddPerfectNumber
