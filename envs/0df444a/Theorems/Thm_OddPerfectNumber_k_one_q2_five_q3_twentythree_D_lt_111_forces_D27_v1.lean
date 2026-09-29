-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T01:59:38.238819+00:00
-- url     : https://prove2.me/theorems/d531720b-d577-4692-be50-f4aa74e08a7b
-- title:
--   Canonical q3=23 small-D reduction to D=27
-- statement:
--   Under the canonical q3=23 small-D hypotheses and accepted exponent floors, the finite abundance and terminal arms force D=27.
-- source:
--   Finite canonical composition: the accepted abundance cut leaves D=27,45,69,75; the accepted D=45 and D=69 windows discharge their branches, and the accepted D=75 terminal uses D<q4.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_abundance_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D69_abundance_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D75_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D_lt_111_forces_D27_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) : D = 27 := by
  sorry

end OddPerfectNumber
