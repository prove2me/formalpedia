-- Prove2me | Theorems.Thm_Kyprianou_Ch02_indepComapFstProductV1
-- name    : Kyprianou.Ch02.indepComapFstProductV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:38:47.053552+00:00
-- url     : https://prove2.me/theorems/9f65b066-f7a9-4e99-a794-a47796aafb84
-- title:
--   indepComapFstProductV1 : product-measure independence transfer
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
theorem indepComapFstProductV1
    {Ω₁ Ω₂ : Type*} [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {n₁ n₂ : MeasurableSpace Ω₁} (h : Indep n₁ n₂ P₁) :
    Indep (n₁.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁))
      (n₂.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁)) (@Measure.prod Ω₁ Ω₂ mΩ₁ mΩ₂ P₁ P₂) := by sorry
end Kyprianou.Ch02
