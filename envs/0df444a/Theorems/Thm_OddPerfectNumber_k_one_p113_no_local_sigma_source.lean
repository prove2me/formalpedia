-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p113_no_local_sigma_source
-- name    : OddPerfectNumber.k_one_p113_no_local_sigma_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T04:24:31.683679+00:00
-- url     : https://prove2.me/theorems/24a8c703-4e3b-4229-8831-59d2dfc67c6e
-- title:
--   The p=113 sigma product has no local source under order obstructions
-- statement:
--   When all four local odd-length geometric sums have order obstructions modulo 113, no local factor is divisible by 113; primality then contradicts 113 dividing their product.
-- source:
--   Apply the accepted order-certificate obstruction to each factor and split prime divisibility across the four-factor product.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

namespace OddPerfectNumber

theorem k_one_p113_no_local_sigma_source (sigma a b c e : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), 587 ^ i))
    (hdiv : 113 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 113) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 113) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 113) ∣ 2 * c + 1)
    (h587 : ¬ orderOf (587 : ZMod 113) ∣ 2 * e + 1) :
    False := by
  sorry

end OddPerfectNumber
