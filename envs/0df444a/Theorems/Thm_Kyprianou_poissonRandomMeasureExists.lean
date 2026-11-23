-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureExists
-- name    : Kyprianou.poissonRandomMeasureExists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:12:26.90797+00:00
-- url     : https://prove2.me/theorems/1de37a23-a90a-47d2-b121-84eb4af8caee
-- title:
--   Theorem 2.4: Poisson random measure existence
-- statement:
--   Construct a time-marked Poisson random measure with intensity dt tensor Π, including finite- and infinite-intensity laws and disjoint-set independence.
-- source:
--   Kyprianou (2006), Theorem 2.4, pp. 39–40

import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem poissonRandomMeasureExists (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure] :
  ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        Nonempty (LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) := by sorry
end Kyprianou
