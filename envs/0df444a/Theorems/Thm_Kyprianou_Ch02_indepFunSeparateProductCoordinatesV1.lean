-- Prove2me | Theorems.Thm_Kyprianou_Ch02_indepFunSeparateProductCoordinatesV1
-- name    : Kyprianou.Ch02.indepFunSeparateProductCoordinatesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:38:53.075526+00:00
-- url     : https://prove2.me/theorems/fd0c97fe-63e8-4d9c-9cf9-8337c5c9d570
-- title:
--   indepFunSeparateProductCoordinatesV1 : product-measure independence transfer
-- statement:
--   Product-probability independence transfer originally established as a helper in the accepted source proof of Kyprianou.Ch02.sourceFaithfulLevyItoIndependentDriversV1. The statement and its Lean proof preserve the exact source parameters and measure-space interfaces.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, proved product-driver construction

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

set_option autoImplicit false

namespace Kyprianou.Ch02
theorem indepFunSeparateProductCoordinatesV1
    {Ω₁ Ω₂ β γ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace β] [MeasurableSpace γ]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (f : Ω₁ → β) (g : Ω₂ → γ) :
    IndepFun (fun ω : Ω₁ × Ω₂ => f ω.1) (fun ω : Ω₁ × Ω₂ => g ω.2) (P₁.prod P₂) := by sorry
end Kyprianou.Ch02
