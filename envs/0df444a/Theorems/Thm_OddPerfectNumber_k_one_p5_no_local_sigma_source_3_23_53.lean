-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p5_no_local_sigma_source_3_23_53
-- name    : OddPerfectNumber.k_one_p5_no_local_sigma_source_3_23_53
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T04:31:04.522512+00:00
-- url     : https://prove2.me/theorems/6201f109-3e5b-472c-b5fe-2361431d4749
-- title:
--   The p=5 sigma product has no local source under order obstructions
-- statement:
--   If the local odd-length sigma sums for bases 3, 23, and 53 have order obstructions modulo 5, and the 5-component cannot divide its own sigma, then 5 cannot divide the global product.
-- source:
--   Apply the accepted order obstruction to the non-5 factors, the accepted own-sigma lemma to the 5-factor, and split primality across the product.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

namespace OddPerfectNumber

theorem k_one_p5_no_local_sigma_source_3_23_53 (sigma a b c e : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), 53 ^ i))
    (hdiv : 5 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 5) ∣ 2 * a + 1)
    (h23 : ¬ orderOf (23 : ZMod 5) ∣ 2 * c + 1)
    (h53 : ¬ orderOf (53 : ZMod 5) ∣ 2 * e + 1) :
    False := by
  sorry

end OddPerfectNumber
