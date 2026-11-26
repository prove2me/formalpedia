-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ShiftStrictPathKernelV1
-- name    : Kyprianou.Ch04.exercise46ShiftStrictPathKernelV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T12:26:23.792681+00:00
-- url     : https://prove2.me/theorems/bbbeaf71-95c7-5072-adad-0a8c437bdf38
-- title:
--   Common strict passage kernel on original and shifted paths
-- statement:
--   Use the same measurable rational passage kernel for original and translated paths.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46ShiftStrictPathKernelV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) :
    ∃ K : Real × (NNReal → Real) → WithTop NNReal, Measurable K ∧
      (∀ x : Real, 0 < x → ∀ w,
        K (x,fun t => L.X t w) = Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w) ∧
      (∀ (w : Omega) (s : NNReal) (x : Real),
        K (x,fun u => L.X (s+u) w - L.X s w) =
          ⨅ u : NNReal, if x < L.X (s+u) w - L.X s w
            then (u : WithTop NNReal) else ⊤) := by
  sorry
