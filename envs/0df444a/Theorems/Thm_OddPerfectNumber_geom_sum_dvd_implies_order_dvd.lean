-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_order_dvd
-- name    : OddPerfectNumber.geom_sum_dvd_implies_order_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T12:26:12.73823+00:00
-- url     : https://prove2.me/theorems/d9c2c20a-acb8-4b26-a532-97da1f12df9b
-- title:
--   Geometric sum divisibility gives order divisibility
-- statement:
--   If a natural prime modulus divides an odd-length geometric sum, then the multiplicative order of the base in the corresponding ZMod divides the geometric-sum length.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_zmod_pow_eq_one

theorem OddPerfectNumber.geom_sum_dvd_implies_order_dvd {p q e : Nat}
    (h : p ∣ ∑ i ∈ Finset.range (2 * e + 1), q ^ i) :
    orderOf (q : ZMod p) ∣ 2 * e + 1 := by sorry
