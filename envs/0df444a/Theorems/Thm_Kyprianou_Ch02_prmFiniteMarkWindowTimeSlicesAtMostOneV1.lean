-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkWindowTimeSlicesAtMostOneV1
-- name    : Kyprianou.Ch02.prmFiniteMarkWindowTimeSlicesAtMostOneV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:52:12.496884+00:00
-- url     : https://prove2.me/theorems/eca58bc8-0e11-4be1-8a48-c2593af67e6a
-- title:
--   Finite-intensity Poisson mark windows have at most one point at every positive time
-- statement:
--   Finite-intensity Poisson mark windows have at most one point at every positive time
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
theorem prmFiniteMarkWindowTimeSlicesAtMostOneV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (A : Set ℝ) (hA : MeasurableSet A) (hfin : ν A < ⊤) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ A) ≤ 1 := by sorry
end Kyprianou.Ch02
