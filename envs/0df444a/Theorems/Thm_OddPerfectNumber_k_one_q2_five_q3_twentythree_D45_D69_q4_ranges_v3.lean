-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T21:56:48.92952+00:00
-- url     : https://prove2.me/theorems/3f196e35-5589-4635-bdd4-248abbb98219
-- title:
--   Canonical q3=23 D=45 and D=69 fourth-prime windows v3
-- statement:
--   The q3=23 D=45 and D=69 small-D survivors satisfy finite q4 upper windows from the strict geometric abundance bound.
-- source:
--   Simplified replacement: only the accepted strict geometric upper bounds are needed for these upper windows; the lower endpoints are exactly D<q4.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v3 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDcases : D = 45 ∨ D = 69) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hDq : D < q4) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) : ((D = 45 ∧ 46 ≤ q4 ∧ q4 ≤ 112) ∨ (D = 69 ∧ 70 ≤ q4 ∧ q4 ≤ 78)) := by
  sorry

end OddPerfectNumber
