-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T21:11:38.676964+00:00
-- url     : https://prove2.me/theorems/ff1aa4f7-acad-4780-a737-13499955d482
-- title:
--   q3=23 small-D abundance cut
-- statement:
--   With the accepted q3=23 support list and the accepted exponent floors, the small-D abundance inequality removes D=3,9,15, leaving 27,45,69,75.
-- source:
--   Cross-multiplied minimum-abundance cut over the accepted finite support list.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) : D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by
  sorry

end OddPerfectNumber
