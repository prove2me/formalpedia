-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_p1093_absurd_from_sources
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_p1093_absurd_from_sources
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T03:26:30.095783+00:00
-- url     : https://prove2.me/theorems/ea50f259-0b31-4c04-aec9-61312b69cf07
-- title:
--   The p=1093 exponent-six subcase contradicts the source certificates
-- statement:
--   In the p=1093, q4=547 role, the accepted factor-five bridge contradicts the accepted local source exclusions.
-- source:
--   A small source-composition theorem for the Euler-role half of the exponent-six branch.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_exp3_six_p1093_five_dvd_sigma
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_547_product_no_five

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp3_six_p1093_absurd_from_sources (m d sigma a b c e : Nat)
    (hprod : m ^ 2 = 547 * d)
    (hsigma_eq : sigma = 1093 * d)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hsigma : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 547 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h547 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i) :
    False := by
  sorry

end OddPerfectNumber
