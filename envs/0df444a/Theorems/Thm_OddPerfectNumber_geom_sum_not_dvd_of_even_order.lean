-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
-- name    : OddPerfectNumber.geom_sum_not_dvd_of_even_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:48:57.954+00:00
-- url     : https://prove2.me/theorems/7bb4920c-bdbe-4147-948e-908a37e34609
-- title:
--   Even order cannot divide an odd geometric-sum length
-- statement:
--   If the multiplicative order of q modulo p is even, then p cannot divide the geometric sum of odd length 2e+1.
-- source:
--   Parity adapter for the accepted geometric-sum-to-order theorem. It is independent of any prime-order evaluator and is intended for finite branch certificates.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_order_dvd

namespace OddPerfectNumber

theorem geom_sum_not_dvd_of_even_order {p q e : Nat}
    (heven : Even (orderOf (q : ZMod p))) :
    ¬ p ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i := by
  sorry

end OddPerfectNumber
