-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_exact_cases
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_exact_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T15:28:37.276964+00:00
-- url     : https://prove2.me/theorems/b57ba0d2-014e-47f2-8427-cf6f1fa77c79
-- title:
--   Canonical q3=23 D=27 fourth-prime exact cases
-- statement:
--   The canonical q3=23 D=27 branch has exactly q4=691, 701, or 709.
-- source:
--   Composition of the accepted canonical lower and upper cuts with the accepted finite prime-window theorem.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_ge_691
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_le_717
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_q4_window_cases

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D27_q4_exact_cases (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 27) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) : q4 = 691 ∨ q4 = 701 ∨ q4 = 709 := by sorry

end OddPerfectNumber
