-- Prove2me | Theorems.Thm_Kyprianou_Ch02_gaussianDriftStationaryIncrementsV1
-- name    : Kyprianou.Ch02.gaussianDriftStationaryIncrementsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:13:53.451798+00:00
-- url     : https://prove2.me/theorems/156d4386-a855-4507-ba52-c0ca376a2411
-- title:
--   gaussianDriftStationaryIncrementsV1
-- statement:
--   Affine drifted Brownian increments: ProbabilityTheory.HasStationaryIncrements
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
theorem gaussianDriftStationaryIncrementsV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0)
 :
    ProbabilityTheory.HasStationaryIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P
    := by sorry
end Kyprianou.Ch02
