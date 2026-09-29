-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_six_cases
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_six_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T15:16:35.612384+00:00
-- url     : https://prove2.me/theorems/3c222c85-a4b7-4b0a-846a-0cbebd644349
-- title:
--   Canonical q3=19 large-D fourth-prime six-case filter
-- statement:
--   The canonical q3=19 large-D bounds and accepted exponent floors reduce q4 to exactly 97, 101, 103, 107, 109, or 113.
-- source:
--   Compose the accepted q4≤113 and q4>89 reductions with the accepted prime enumeration, then normalize the finite disjunction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_le_113_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_gt_89
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_prime_cases

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_large_D_q4_six_cases (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 225 ≤ D) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : q4 = 97 ∨ q4 = 101 ∨ q4 = 103 ∨ q4 = 107 ∨ q4 = 109 ∨ q4 = 113 := by sorry

end OddPerfectNumber
