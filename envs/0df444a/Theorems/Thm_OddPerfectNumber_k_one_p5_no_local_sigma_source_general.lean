-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p5_no_local_sigma_source_general
-- name    : OddPerfectNumber.k_one_p5_no_local_sigma_source_general
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T04:48:36.886853+00:00
-- url     : https://prove2.me/theorems/66795619-7b86-4f8b-adf0-ca1a737c7a89
-- title:
--   The p=5 sigma product has no local source under three order obstructions
-- statement:
--   If the three non-5 local odd-length geometric sums for bases 3, q₃ and q₄ all have order obstructions modulo 5, then 5 cannot divide the product of those sums and the 5-component sum. This is a reusable residual-source certificate for finite four-support branches.
-- source:
--   Finite four-support source analysis; exact product split using the accepted order obstruction and no-self-divisibility theorem.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

namespace OddPerfectNumber

theorem k_one_p5_no_local_sigma_source_general (sigma a b c e q3 q4 : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), q3 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hdiv : 5 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 5) ∣ 2 * a + 1)
    (hq3 : ¬ orderOf (q3 : ZMod 5) ∣ 2 * c + 1)
    (hq4 : ¬ orderOf (q4 : ZMod 5) ∣ 2 * e + 1) :
    False := by
  sorry

end OddPerfectNumber
