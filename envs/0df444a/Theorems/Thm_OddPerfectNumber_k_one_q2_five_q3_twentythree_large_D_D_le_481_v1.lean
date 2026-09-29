-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_D_le_481_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_D_le_481_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T08:30:59.529329+00:00
-- url     : https://prove2.me/theorems/ba67d32b-4b4c-4942-b989-c9c3c7a70b84
-- title:
--   q3=23 upper D bound independent of fourth-prime divisibility
-- statement:
--   Let m, a, b, c, e, D, p and q4 be natural numbers with D positive and q4 a prime at least 53. Suppose m squared has factorization 3^(2a) 5^(2b) 23^(2c) q4^(2e), sigma is the product of the corresponding four geometric sums, D sigma = p m squared, and p = 2D - 1. Then D is at most 481. This upper envelope does not require the fourth prime to divide D and is used in the remaining q3=23 canonical reduction.
-- source:
--   Intermediate inequality for the existing q3=23 branch, parent OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_canonical_v13 (d97d0664-bdac-4cdf-bbe4-20e427aa39cb). Derived from accepted geom_sum_cross_lt_of_le (c7beccbd-6011-44fc-9a95-6d878b9470e0): 9152*sigma<18285*m², so 9152*(2D-1)<18285*D. No dependence on the parent or its finite/source reductions.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_D_le_481_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDpos : 0 < D)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4ge : 53 ≤ q4) : D ≤ 481 := by
  sorry

end OddPerfectNumber
