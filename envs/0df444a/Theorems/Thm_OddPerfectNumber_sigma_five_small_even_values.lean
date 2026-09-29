-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_five_small_even_values
-- name    : OddPerfectNumber.sigma_five_small_even_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T18:38:22.114987+00:00
-- url     : https://prove2.me/theorems/91f8e9b0-3fe3-464b-a342-3ec7dbaf2e95
-- title:
--   Exact local sigma values for 5 at exponents 2, 4, and 6
-- statement:
--   The local geometric sums for the prime 5 at the even exponents 2, 4, and 6 are respectively 31, 781, and 19531.
-- source:
--   Exact arithmetic certificates used by the finite q2=5 branch: sigma(5^2)=31, sigma(5^4)=781=11*71, and sigma(5^6)=19531.

import Mathlib

namespace OddPerfectNumber

theorem sigma_five_small_even_values :
    ((∑ i ∈ Finset.range (2 + 1), 5 ^ i) = 31) ∧
    ((∑ i ∈ Finset.range (4 + 1), 5 ^ i) = 781) ∧
    ((∑ i ∈ Finset.range (6 + 1), 5 ^ i) = 19531) := by sorry

end OddPerfectNumber
