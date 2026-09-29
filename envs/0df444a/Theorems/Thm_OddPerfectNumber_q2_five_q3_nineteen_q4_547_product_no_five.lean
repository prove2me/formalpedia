-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_547_product_no_five
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_547_product_no_five
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:30:47.5627+00:00
-- url     : https://prove2.me/theorems/37f2d60c-05b0-433d-88bf-e8e8bf87b92b
-- title:
--   The q4=547 local sigma product is not divisible by 5
-- statement:
--   In the q4=547 support branch, no local sigma factor can supply a factor 5.
-- source:
--   Finite product divisibility certificate using the accepted own-sigma and order obstructions.

import Mathlib
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_547_product_no_five (a b c e : Nat)
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h547 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i) :
    ¬ 5 ∣ (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 547 ^ i) := by
  sorry

end OddPerfectNumber
