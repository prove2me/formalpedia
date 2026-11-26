-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ZeroDiscountIndicatorV1
-- name    : Kyprianou.Ch04.exercise46ZeroDiscountIndicatorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:26:32.029251+00:00
-- url     : https://prove2.me/theorems/fa3895fa-b2db-40a3-87a6-49e4c1ff55f0
-- title:
--   Zero-discount passage reward is a finite-clock indicator
-- statement:
--   Zero-discount passage reward is a finite-clock indicator
-- source:
--   Kyprianou (2006), Exercise 4.6.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46ZeroDiscountIndicatorV1
    (b : WithTop NNReal) :
    (if b = ⊤ then (0 : Real)
      else Real.exp (-0 * ((b.untopD 0 : NNReal) : Real))) =
      (if b = ⊤ then 0 else 1) := by
  sorry
