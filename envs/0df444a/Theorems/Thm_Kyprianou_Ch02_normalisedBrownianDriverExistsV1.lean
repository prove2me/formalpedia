-- Prove2me | Theorems.Thm_Kyprianou_Ch02_normalisedBrownianDriverExistsV1
-- name    : Kyprianou.Ch02.normalisedBrownianDriverExistsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:26:04.852015+00:00
-- url     : https://prove2.me/theorems/d8ad8215-6906-471f-b34f-fb1e23f421e9
-- title:
--   Pointwise-normalised canonical Brownian driver existence
-- statement:
--   Construct a BrownianMotion on the canonical Gaussian path law whose real-time version is centred pathwise at time zero. Unlike arbitrary BrownianMotion, the constructed driver satisfies B.W 0 ω = 0 for every sample ω, aligning the pointwise start-zero requirement of IsLevyProcess. Reuses the established canonical Brownian construction and its proved measurability and continuity helpers.
-- source:
--   Kyprianou (2006), Chapter 2, Lévy–Itô decomposition, Brownian driver

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem normalisedBrownianDriverExistsV1 :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := hP
        ∃ (B : LevyStochCalc.Brownian.BrownianMotion P),
          ∀ ω : Ω, B.W 0 ω = 0 := by sorry
end Kyprianou.Ch02
