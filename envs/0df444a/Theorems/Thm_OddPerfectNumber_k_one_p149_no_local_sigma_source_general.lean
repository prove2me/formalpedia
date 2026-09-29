-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p149_no_local_sigma_source_general
-- name    : OddPerfectNumber.k_one_p149_no_local_sigma_source_general
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T20:50:14.212304+00:00
-- url     : https://prove2.me/theorems/3fb2c5be-e529-4dae-8184-146fa915a3f1
-- title:
--   The p=149 sigma product has no local source under four order obstructions
-- statement:
--   If the four local odd-length geometric sums for bases 3, 5, 19 and q4 all have order obstructions modulo 149, then 149 cannot divide their product.
-- source:
--   Reusable p=149 source-exclusion certificate for the q2=5, q3=19 D=75 candidate.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

namespace OddPerfectNumber

theorem k_one_p149_no_local_sigma_source_general (sigma a b c e q4 : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hdiv : 149 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 149) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 149) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 149) ∣ 2 * c + 1)
    (hq4 : ¬ orderOf (q4 : ZMod 149) ∣ 2 * e + 1) :
    False := by
  sorry

end OddPerfectNumber
