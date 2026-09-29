-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p113_no_local_sigma_source_general
-- name    : OddPerfectNumber.k_one_p113_no_local_sigma_source_general
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T04:40:53.536304+00:00
-- url     : https://prove2.me/theorems/475112d8-11b8-4f56-8526-31665074b7df
-- title:
--   The p=113 sigma product has no local source under four order obstructions
-- statement:
--   If the four local odd-length geometric sums for bases 3, 5, 19 and q₄ all have order obstructions modulo 113, then 113 cannot divide their product. This is the reusable source-exclusion certificate for the q₂=5, q₃=19, D=57 candidates whose fourth support prime is not 587.
-- source:
--   Finite q₂=5, q₃=19 source analysis; exact order-obstruction proof using the accepted geometric-sum theorem.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

namespace OddPerfectNumber

theorem k_one_p113_no_local_sigma_source_general (sigma a b c e q4 : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hdiv : 113 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 113) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 113) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 113) ∣ 2 * c + 1)
    (hq4 : ¬ orderOf (q4 : ZMod 113) ∣ 2 * e + 1) :
    False := by
  sorry

end OddPerfectNumber
