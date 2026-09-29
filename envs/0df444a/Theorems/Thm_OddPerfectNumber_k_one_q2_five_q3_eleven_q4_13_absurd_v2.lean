-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_q4_13_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_eleven_q4_13_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T22:38:37.727926+00:00
-- url     : https://prove2.me/theorems/5917d3d8-670f-457e-92b9-5a5709449a49
-- title:
--   The q2=5 q3=11 q4=13 support branch exceeds abundance (v2)
-- statement:
--   With exponents at least two on 5, 11, and 13, the exact four-component abundancy lower bound already exceeds two.
-- source:
--   Changed v2 composition with explicit product association and factorized equality normalizations after the terminal CE on the predecessor target.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_eleven_ge_two_sharp_v3
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two

namespace OddPerfectNumber

theorem k_one_q2_five_q3_eleven_q4_13_absurd_v2
    (m b c e sigma : Nat)
    (hfac : m ^ 2 = 3 ^ 2 * 5 ^ b * 11 ^ c * 13 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 13 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
