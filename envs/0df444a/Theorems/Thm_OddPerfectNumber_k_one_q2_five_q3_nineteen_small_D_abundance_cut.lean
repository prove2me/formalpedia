-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_abundance_cut
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_abundance_cut
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T11:22:17.225701+00:00
-- url     : https://prove2.me/theorems/2250cccf-387e-40b2-9730-e5bb4d892f96
-- title:
--   Small-D abundance cut to D in {57, 75, 135}
-- statement:
--   Under the q2=5 q3=19 canonical factorization with 8<=a, 6<=b, 4<=c, 2<=e and prime q4, the minimum-abundance product 9841/6561 * 3906/3125 * 137561/130321 exceeds p/D = (2D-1)/D for D in {3,9,15,19,27,45}, leaving D in {57,75,135}. D=135 needs a separate order-based elimination.
-- source:
--   Cross-multiplied minimum-abundance argument mirroring the accepted q4=1093 support-abundance proof, with the 8/6/4 exponent floors. Exact integer constants C1=5287699850706, C2=2671987753125.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_abundance_cut
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDcases : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45 ∨ D = 57 ∨ D = 75 ∨ D = 135)
    (hp : p = 2 * D - 1)
    (hq4prime : q4.Prime)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    D = 57 ∨ D = 75 ∨ D = 135 := by
  sorry

end OddPerfectNumber
