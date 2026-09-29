-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p5_no_local_sigma_source_general_v2
-- name    : OddPerfectNumber.k_one_p5_no_local_sigma_source_general_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T01:20:17.103589+00:00
-- url     : https://prove2.me/theorems/5db57dc3-c16b-4506-80da-e8d1a2fcf788
-- title:
--   A factor five cannot enter this four-factor sigma product
-- statement:
--   If the 3-, q3-, and q4-components have no odd-length source for 5, then 5 cannot divide the four-factor sigma product because the 5-component cannot divide its own sigma.
-- source:
--   Generic finite source dispatch obtained by factoring 5 through the product and applying the accepted order-divisor obstruction to the three non-self components.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

namespace OddPerfectNumber

theorem k_one_p5_no_local_sigma_source_general_v2 (sigma a b c e q3 q4 : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), q3 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hdiv : 5 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 5) ∣ 2 * a + 1)
    (hq3 : ¬ orderOf (q3 : ZMod 5) ∣ 2 * c + 1)
    (hq4 : ¬ orderOf (q4 : ZMod 5) ∣ 2 * e + 1) :
    False := by
  sorry

end OddPerfectNumber
