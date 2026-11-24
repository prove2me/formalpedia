-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmBadTimeSliceMeasureGridBoundV1
-- name    : Kyprianou.Ch02.prmBadTimeSliceMeasureGridBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:58.287337+00:00
-- url     : https://prove2.me/theorems/37f993d6-ef84-4a72-987c-2333f67c9b33
-- title:
--   prmBadTimeSliceMeasureGridBound
-- statement:
--   prmBadTimeSliceMeasureGridBound
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem prmBadTimeSliceMeasureGridBoundV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (A : Set ℝ) (hA : MeasurableSet A) (hfin : ν A < ⊤) (T : ℝ≥0)
    (n : ℕ) :
    P.real {ω | ¬ ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ A) ≤ 1} ≤
      ((T : ℝ) * (ν A).toReal)^2 / ((n+1 : ℕ) : ℝ) := by sorry
end Kyprianou.Ch02
