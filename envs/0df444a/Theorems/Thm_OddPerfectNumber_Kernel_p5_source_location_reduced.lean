-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_p5_source_location_reduced
-- name    : OddPerfectNumber.Kernel.p5_source_location_reduced
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T08:49:13.139985+00:00
-- url     : https://prove2.me/theorems/01a29738-d641-4613-80da-2f926331ff60
-- title:
--   Prime-source localization in the explicit p=5 branch
-- statement:
--   If a prime source divides the explicit p=5 first-equation shape m=651*d1, and it is neither 3 nor 7, then it is the middle-block prime 31 or divides the free square component d1. This is the source-location bridge used after excluding the final-block source and the 3-source.
-- source:
--   Specialization of the Proved five_two_prime_source_location_disjunction to the explicit p=5 tuple m=651*d1; the child isolates the remaining source classes for the second-Dris analysis.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem p5_source_location_reduced (d1 t : Nat)
    (ht : t.Prime) (htm : t ∣ 651 * d1)
    (ht3 : t ≠ 3) (ht7 : t ≠ 7) :
    t = 31 ∨ t ∣ d1 := by
  sorry

end OddPerfectNumber.Kernel
