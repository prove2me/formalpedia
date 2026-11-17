-- Prove2me | Theorems.Thm_Kyprianou_Ch07_positiveInfiniteMeanContinuousTimeLevyStrongLaw
-- name    : Kyprianou.Ch07.positiveInfiniteMeanContinuousTimeLevyStrongLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:11:13.722199+00:00
-- url     : https://prove2.me/theorems/b771fe3b-9109-4cc0-a12b-841ee50de85e
-- title:
--   Exercise 7.2(iv): continuous-time strong law with positive infinite mean
-- statement:
--   With infinite positive mean and finite negative part, truncate positive jumps at increasing levels, prove positive drift for each truncated process, and pass to a diagonal monotone lower bound.
-- source:
--   Kyprianou (2006), Chapter 7, Exercise 7.2, printed p. 207; original PDF p. 216; source solution original PDF pp. 343–344. Exact conjunct isolated from the published complete Exercise 7.2 source proposition 1c79cede-86f1-4d46-b811-93526a74814d.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.positiveInfiniteMeanContinuousTimeLevyStrongLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hMean : Kyprianou.Ch07.positiveMeanPart P X = ⊤ ∧
      Kyprianou.Ch07.negativeMeanPart P X < ⊤) :
    ∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => X t omega / (t : Real))
        atTop atTop := by
  sorry
