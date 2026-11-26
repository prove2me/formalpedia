-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BoundedStoppedMarkV1
-- name    : Kyprianou.Ch04.exercise46BoundedStoppedMarkV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:05:46.139477+00:00
-- url     : https://prove2.me/theorems/283a1b81-0386-5dae-94f8-c1ebcd050053
-- title:
--   Bounded stopping time evaluation of physical service mark
-- statement:
--   Evaluate the right-continuous path at the bounded stopping time and its left limit on the path capped at the deterministic horizon; the resulting service mark is measurable at that horizon.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BoundedStoppedMarkV1
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (a : Omega → NNReal) (ha : IsStoppingTime G.rightCont (fun w => (a w : WithTop NNReal)))
    (T : NNReal) (hT : ∀ w, a w ≤ T) :
    Measurable[G.rightCont T] (fun w =>
      -(L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w))) := by
  sorry
