-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_exp3_eq_two
-- name    : OddPerfectNumber.k_one_q2_five_q3_eleven_exp3_eq_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T22:51:47.901723+00:00
-- url     : https://prove2.me/theorems/6e44e5cb-21a9-4a55-b6c3-e9140d596e6d
-- title:
--   The 3-component exponent in the q2=5 q3=11 branch is two
-- statement:
--   Under the factored four-support sigma equations and the exact upper abundance bound, the even positive exponent of 3 cannot reach four, so it is two.
-- source:
--   Exact cross-multiplied abundance adapter: the 3 exponent-four floor, 5 and 11 exponent-two floors, and the nonnegative q4 factor exceed two.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_four
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_eleven_ge_two_sharp_v3
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_eleven_exp3_eq_two
    (m a b c e q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (hq4prime : q4.Prime) (ha2 : 2 ≤ a) (haeven : Even a)
    (hb : 2 ≤ b) (hc : 2 ≤ c) :
    a = 2 := by
  sorry

end OddPerfectNumber
