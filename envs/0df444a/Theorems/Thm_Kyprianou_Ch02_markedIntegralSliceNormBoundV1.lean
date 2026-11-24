-- Prove2me | Theorems.Thm_Kyprianou_Ch02_markedIntegralSliceNormBoundV1
-- name    : Kyprianou.Ch02.markedIntegralSliceNormBoundV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:56:08.196592+00:00
-- url     : https://prove2.me/theorems/94eb5e60-8331-45c2-8df2-dafac2741698
-- title:
--   markedIntegralSliceNormBound
-- statement:
--   markedIntegralSliceNormBound
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
theorem markedIntegralSliceNormBoundV1
    (μ : Measure (ℝ × ℝ)) (A : Set ℝ) (hA : MeasurableSet A)
    (hsmall : ∀ x ∈ A, |x| < 1)
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T) (c : ℝ) (hc : 0 ≤ c)
    (hcut : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
      {x : ℝ | c < |x| ∧ |x| < 1}) = 0)
    (hslice : μ ({(t : ℝ)} ×ˢ A) ≤ 1) :
    |∫ z in {(t : ℝ)} ×ˢ A, z.2 ∂μ| ≤ c := by sorry
end Kyprianou.Ch02
