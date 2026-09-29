-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_of_factorization
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_31_abundance_of_factorization
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:29:52.289619+00:00
-- url     : https://prove2.me/theorems/9b491cbd-b806-4019-8172-14911da34b1e
-- title:
--   The q4=31 factorization certificate contradicts the canonical upper bound
-- statement:
--   Given the exact four-prime factorization and sigma product for support {3,5,19,31}, exponents a≥6,c,e≥2 make sigma strictly exceed twice the square, contradicting the canonical deficient upper bound.
-- source:
--   Branch-facing certificate interface: the factorization and sigma-product equalities are the standard accepted four-support bookkeeping, while hupper is the integer form of sigma(m²)<2m². The monotone local abundance theorem supplies the contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_monotone

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_31_abundance_of_factorization (m a c e sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ 2 * 19 ^ c * 31 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 31 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (ha : 6 ≤ a) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
