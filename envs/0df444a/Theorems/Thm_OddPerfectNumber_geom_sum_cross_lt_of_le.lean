-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
-- name    : OddPerfectNumber.geom_sum_cross_lt_of_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T12:10:42.039134+00:00
-- url     : https://prove2.me/theorems/c7beccbd-6011-44fc-9a95-6d878b9470e0
-- title:
--   Scaled geometric-sum upper bound under an ordered base
-- statement:
--   If 2 ≤ r ≤ q and q is prime, then the geometric sum in base q satisfies (r−1)(1+q+⋯+q^a) < r q^a. This is the scaled integer form used in finite-support abundancy bounds.
-- source:
--   Elementary consequence of OddPerfectNumber.prime_power_sigma_euler_upper_bound and q ≥ r.

import Mathlib
import Theorems.Thm_OddPerfectNumber_prime_power_sigma_euler_upper_bound

namespace OddPerfectNumber

theorem geom_sum_cross_lt_of_le (r q a : Nat)
    (hr : 2 ≤ r) (hrq : r ≤ q) (hq : q.Prime) :
    (r - 1) * (∑ i ∈ Finset.range (a + 1), q ^ i) <
      r * q ^ a := by sorry

end OddPerfectNumber
