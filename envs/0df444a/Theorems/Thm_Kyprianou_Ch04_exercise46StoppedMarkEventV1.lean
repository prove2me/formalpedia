-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46StoppedMarkEventV1
-- name    : Kyprianou.Ch04.exercise46StoppedMarkEventV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:06:55.129609+00:00
-- url     : https://prove2.me/theorems/78f6c0ff-f37a-5095-973b-d949ab07da04
-- title:
--   Physical service-mark event is measurable up to the stopping time
-- statement:
--   Truncate the stopping clock at T. On the event that the original clock is at most T its physical service mark agrees with the bounded stopped mark, hence the intersected event is measurable at T.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46StoppedMarkEventV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (C : Set Real) (hC : MeasurableSet C) (T : NNReal) :
    let J : Omega → Real := fun w =>
      -(L.X ((A w).untopD 0) w - Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0))
    MeasurableSet[G.rightCont T] (J ⁻¹' C ∩ {w | A w ≤ (T : WithTop NNReal)}) := by
  sorry
