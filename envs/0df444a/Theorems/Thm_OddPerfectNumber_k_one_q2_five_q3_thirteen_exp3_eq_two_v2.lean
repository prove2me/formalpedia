-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp3_eq_two_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_eq_two_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T03:41:39.807478+00:00
-- url     : https://prove2.me/theorems/099a5d9d-3ba9-4ac1-888d-3f6d8055ea96
-- title:
--   The 3-component exponent in the q2=5 q3=13 branch is two
-- statement:
--   The accepted q2=5,q3=13 abundance certificate rules out every even 3-exponent at least four, so a positive even exponent is exactly two.
-- source:
--   Use parity and positivity to turn a != 2 into a >= 4, then apply the accepted generic abundance contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_exp3_eq_two_v2 (m a b c e q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 13 ^ c * q4 ^ e)
    (hsigma : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 13 ^ i) * (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (ha2 : 2 ≤ a) (haeven : Even a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    a = 2 := by
  sorry

end OddPerfectNumber
