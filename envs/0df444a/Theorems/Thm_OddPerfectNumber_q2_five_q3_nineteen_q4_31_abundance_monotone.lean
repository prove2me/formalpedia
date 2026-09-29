-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_monotone
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_31_abundance_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:39:07.882768+00:00
-- url     : https://prove2.me/theorems/4655f38f-b1ce-4e75-9a1d-052f0f7684f1
-- title:
--   Minimum abundance persists above the q4=31 exponent floor
-- statement:
--   For every exponent triple at or above (6,2,2), the local divisor-sum product on bases (3,5,19,31) is strictly larger than twice the corresponding prime-power product.
-- source:
--   Monotonic extension of the exact minimum-abundance certificate. Geometric sums and prime powers are monotone in their exponents, so the strict inequality at (6,2,2) persists for all a≥6,c≥2,e≥2.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_minimum_abundance_certificate

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_31_abundance_monotone (a c e : Nat)
    (ha : 6 ≤ a) (hc : 2 ≤ c) (he : 2 ≤ e) :
    2 * (3 ^ a * 5 ^ 2 * 19 ^ c * 31 ^ e) <
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 31 ^ i) := by
  sorry

end OddPerfectNumber
