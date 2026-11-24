-- Prove2me | Theorems.Thm_Kyprianou_Ch02_markedIntegralLeftLimitFromFiniteWindowV1
-- name    : Kyprianou.Ch02.markedIntegralLeftLimitFromFiniteWindowV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:57.234306+00:00
-- url     : https://prove2.me/theorems/99df5d14-fbde-4b26-a0e6-55c1f4520110
-- title:
--   markedIntegralLeftLimitFromFiniteWindow
-- statement:
--   markedIntegralLeftLimitFromFiniteWindow
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
theorem markedIntegralLeftLimitFromFiniteWindowV1
    (μ : Measure (ℝ × ℝ)) (A : Set ℝ) (hA : MeasurableSet A)
    (hsmall : ∀ x ∈ A, |x| < 1)
    (T t : ℝ≥0) (htT : t ≤ T)
    (hfin : μ (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A) < ⊤) :
    Tendsto (fun s : ℝ≥0 => ∫ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ A, z.2 ∂μ)
      (nhdsWithin t (Set.Iio t))
      (nhds (∫ z in Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ A, z.2 ∂μ)) := by sorry
end Kyprianou.Ch02
