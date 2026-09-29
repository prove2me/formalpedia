-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_le_717
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_le_717
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T14:11:48.32126+00:00
-- url     : https://prove2.me/theorems/e4ab7349-da37-4ff5-999c-3addc63eb524
-- title:
--   Canonical q3=23 D=27 fourth-prime upper cut
-- statement:
--   In the canonical q3=23 D=27 branch, strict upper abundance forces q4≤717.
-- source:
--   If q4>717, primality is not needed beyond q4≥718. Multiply the strict geometric-sum bounds with r=3,5,23,718 and combine 53 m²≤27 sigma from the Euler relation. The exact constants differ by six, giving a contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D27_q4_le_717 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4) :
    q4 ≤ 717 := by
  sorry

end OddPerfectNumber
