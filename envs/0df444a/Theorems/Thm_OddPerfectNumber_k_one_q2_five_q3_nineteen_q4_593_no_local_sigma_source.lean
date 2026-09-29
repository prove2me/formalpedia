-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_593_no_local_sigma_source
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_593_no_local_sigma_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T20:17:50.386775+00:00
-- url     : https://prove2.me/theorems/32740de9-cef2-4a79-ae2f-e8d75e996ddf
-- title:
--   The q3=19 q4=593 sigma product has no source
-- statement:
--   With exact even-order obstructions for 3,5,19 modulo 593, and the own-sigma obstruction for 593, the q4=593 product cannot be divisible by 593.
-- source:
--   Product-divisor split using the accepted generic geometric-sum order obstruction and own-prime sigma obstruction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_593_no_local_sigma_source (sigma a b c e : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), 593 ^ i))
    (hdiv : 593 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 593) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 593) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 593) ∣ 2 * c + 1) :
    False := by
  sorry

end OddPerfectNumber
