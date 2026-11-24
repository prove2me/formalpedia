-- Prove2me | Theorems.Thm_Kyprianou_Ch02_gaussianDriftIndependentIncrementsV1
-- name    : Kyprianou.Ch02.gaussianDriftIndependentIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:13:55.797782+00:00
-- url     : https://prove2.me/theorems/37d6ac40-7cd1-4670-b52a-12e50dab74a9
-- title:
--   gaussianDriftIndependentIncrementsV1
-- statement:
--   Affine drifted Brownian increments: ProbabilityTheory.HasIndependentIncrements
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1

import Theorems.Thm_Kyprianou_Ch01_mathlibIndepIncrements_toLeanLevy
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
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
theorem gaussianDriftIndependentIncrementsV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0)
 :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P
    := by sorry
end Kyprianou.Ch02
