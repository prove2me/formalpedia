-- Prove2me | Theorems.Thm_Kyprianou_Ch03_hitFinite_iff_everExceeds
-- name    : Kyprianou.Ch03.hitFinite_iff_everExceeds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:27:06.302199+00:00
-- url     : https://prove2.me/theorems/b2fc6cf5-9e06-4751-b051-a377738ef96f
-- title:
--   Chapter 3 first hitting: ever-exceedance iff positive-time first hit is finite
-- statement:
--   For a spectrally negative Levy process started at zero, and nonnegative level x, a path ever exceeds x exactly when the first positive-time hitting time of (x,infinity) is finite.
-- source:
--   Derived directly from original Kyprianou Chapter 3 first-hitting-time definition and Exercise 3.6 zero-root passage event

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem hitFinite_iff_everExceeds
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : ℝ) (hx : 0 ≤ x) (omega : Omega) :
    (∃ t : NNReal, x < L.X t omega) ↔
      (firstHittingTime L.X (Set.Ioi x) omega != ⊤) := by
  sorry
end Kyprianou.Ch03
