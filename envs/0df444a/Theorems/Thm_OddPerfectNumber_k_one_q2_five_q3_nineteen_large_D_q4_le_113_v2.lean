-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_le_113_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_le_113_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T13:58:33.416815+00:00
-- url     : https://prove2.me/theorems/050dc9f2-902e-49c8-959e-e39eb9c2ad28
-- title:
--   Canonical q3=19 large-D fourth-prime upper cut v2
-- statement:
--   In the canonical q2=5,q3=19 branch with D≥225, the fourth support prime cannot exceed 113; otherwise the strict four-factor geometric-sum upper bound contradicts the half-successor lower bound.
-- source:
--   For q4>113, primality forces q4≥127. Apply the strict geometric-sum bounds with bases 3,5,19,127, multiply them, and combine the resulting upper bound with 449 m²≤225 sigma from D≥225 and p=2D−1. The exact cross-multiplied constants are contradictory.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_large_D_q4_le_113_v2 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 225 ≤ D) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4) :
    q4 ≤ 113 := by
  sorry

end OddPerfectNumber
