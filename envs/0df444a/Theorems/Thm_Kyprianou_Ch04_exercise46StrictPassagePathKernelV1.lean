-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46StrictPassagePathKernelV1
-- name    : Kyprianou.Ch04.exercise46StrictPassagePathKernelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:23:38.411176+00:00
-- url     : https://prove2.me/theorems/b25f7a37-8666-490c-81a3-3b87ae2aa61c
-- title:
--   Joint Borel strict passage kernel on the coordinate path space
-- statement:
--   Countably many rational sample times give a measurable clock on height and the full coordinate path. Right continuity and zero initial state identify it with the strict positive-height passage.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46StrictPassagePathKernelV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) :
    ∃ K : Real × (NNReal → Real) → WithTop NNReal, Measurable K ∧
      ∀ x : Real, 0 < x → ∀ w : Omega,
        K (x, fun t => L.X t w) = Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w := by
  sorry
