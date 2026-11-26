-- Prove2me | Theorems.Thm_Kyprianou_Ch04_strictSublevelStoppingTime
-- name    : Kyprianou.Ch04.strictSublevelStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:07:10.580382+00:00
-- url     : https://prove2.me/theorems/2ef0f82e-0cf0-5666-b659-bfb6006e1930
-- title:
--   strictSublevelStoppingTime
-- statement:
--   For a right-continuous filtration, measurability of all strict time sublevels implies the stopping-time property.
-- source:
--   Kyprianou (2006), Exercise 4.3(i), pp. 106-107.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Right-continuity upgrades strict sublevel measurability to a stopping time. -/
theorem Kyprianou.Ch04.strictSublevelStoppingTime {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hRC : F.IsRightContinuous) (tau : Omega → WithTop NNReal)
    (hlt : ∀ s : NNReal, MeasurableSet[F s] {w | tau w < (s : WithTop NNReal)}) :
    IsStoppingTime F tau := by
  sorry
