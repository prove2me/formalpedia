-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_gt_89
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_gt_89
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T14:27:12.659289+00:00
-- url     : https://prove2.me/theorems/846b3c28-d271-42f4-b3e6-6dc20d7a3927
-- title:
--   Canonical q3=19 large-D fourth-prime lower cut
-- statement:
--   Under the canonical q3=19 large-D factorization and exponent floors, q4≤89 makes the minimum four-factor abundancy exceed 2, contradicting the half-successor relation.
-- source:
--   Multiply the accepted 3,5,19 lower bounds with the uniform two-last-terms bound for q4≤89; the resulting rational lower bound is strictly greater than 2, while p=2D−1 makes sigma/m²<2.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_large_D_q4_gt_89 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 225 ≤ D) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hq4le : q4 ≤ 89) :
    False := by
  sorry

end OddPerfectNumber
