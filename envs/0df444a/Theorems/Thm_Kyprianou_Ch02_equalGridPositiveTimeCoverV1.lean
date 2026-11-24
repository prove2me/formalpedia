-- Prove2me | Theorems.Thm_Kyprianou_Ch02_equalGridPositiveTimeCoverV1
-- name    : Kyprianou.Ch02.equalGridPositiveTimeCoverV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:56:00.421652+00:00
-- url     : https://prove2.me/theorems/eafd1fdc-67f3-422b-954e-a6ad9378949f
-- title:
--   equalGridPositiveTimeCover
-- statement:
--   equalGridPositiveTimeCover
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
theorem equalGridPositiveTimeCoverV1
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    let d : ℝ := (T : ℝ) / ((n+1 : ℕ) : ℝ)
    ∃ k : ℕ, k < n+1 ∧
      (t : ℝ) ∈ Set.Ioc ((k : ℝ) * d) (((k+1 : ℕ) : ℝ) * d) := by sorry
end Kyprianou.Ch02
