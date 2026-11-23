-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoIndependentDriversNormalisedV1
-- name    : Kyprianou.Ch02.sourceFaithfulLevyItoIndependentDriversNormalisedV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T21:20:33.031131+00:00
-- url     : https://prove2.me/theorems/ffde4e82-3517-446f-a270-150f4567cd8e
-- title:
--   Construct mutually independent Brownian and Poisson drivers with a Brownian path normalised to start at zero at every sample point
-- statement:
--   Construct mutually independent Brownian and Poisson drivers with a Brownian path normalised to start at zero at every sample point
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, normalized Brownian drivers

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

theorem sourceFaithfulLevyItoIndependentDriversNormalisedV1
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure),
          ProbabilityTheory.IndepFun
            (fun ω => fun (t : ℝ) => B.W t ω)
            (fun ω => N.N ω) P ∧
          (∀ ω : Ω, B.W 0 ω = 0) := by sorry

end Kyprianou.Ch02
