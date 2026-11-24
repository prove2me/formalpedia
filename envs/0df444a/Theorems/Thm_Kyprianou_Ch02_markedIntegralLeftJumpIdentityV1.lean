-- Prove2me | Theorems.Thm_Kyprianou_Ch02_markedIntegralLeftJumpIdentityV1
-- name    : Kyprianou.Ch02.markedIntegralLeftJumpIdentityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:55:57.942042+00:00
-- url     : https://prove2.me/theorems/5e3ef8bd-1764-47ea-bd33-00471dccd48c
-- title:
--   markedIntegralLeftJumpIdentity
-- statement:
--   markedIntegralLeftJumpIdentity
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
theorem markedIntegralLeftJumpIdentityV1
    (μ : Measure (ℝ × ℝ)) (A : Set ℝ) (hA : MeasurableSet A)
    (hsmall : ∀ x ∈ A, |x| < 1) (t : ℝ≥0) (ht : 0 < t)
    (hfin : μ (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A) < ⊤) :
    (∫ z in Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ) -
      (∫ z in Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ) =
      ∫ z in {(t : ℝ)} ×ˢ A, z.2 ∂μ := by sorry
end Kyprianou.Ch02
