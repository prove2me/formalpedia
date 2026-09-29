-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
-- name    : OddPerfectNumber.geom_sum_not_dvd_of_order_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T12:29:32.606362+00:00
-- url     : https://prove2.me/theorems/cf4ce21e-b8bb-4dc2-b95c-c36116758128
-- title:
--   Order certificate excludes geometric-sum divisibility
-- statement:
--   If the multiplicative order of the base modulo p does not divide an odd geometric-sum length, then p cannot divide that geometric sum.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_order_dvd

theorem OddPerfectNumber.geom_sum_not_dvd_of_order_certificate {p q e : Nat}
    (hord : ¬ orderOf (q : ZMod p) ∣ 2 * e + 1) :
    ¬ p ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i := by sorry
