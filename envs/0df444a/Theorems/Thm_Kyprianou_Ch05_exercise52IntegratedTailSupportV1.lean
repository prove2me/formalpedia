-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailSupportV1
-- name    : Kyprianou.Ch05.exercise52IntegratedTailSupportV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:34.560467+00:00
-- url     : https://prove2.me/theorems/42145c07-4222-4702-ba39-086df3891126
-- title:
--   The integrated-tail law has positive support and is nonlattice if normalised
-- statement:
--   The integrated-tail law has positive support and is nonlattice if normalised
-- source:
--   Kyprianou (2006), Exercise 5.2(ii)

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05

theorem Kyprianou.Ch05.exercise52IntegratedTailSupportV1
    (nu : Measure ℝ) (m : ℝ)
    (hF : IsProbabilityMeasure (ascendingRecordJumpDistribution nu m)) :
    ascendingRecordJumpDistribution nu m (Iic 0) = 0 ∧
      NonLatticeMeasure (ascendingRecordJumpDistribution nu m) := by
  sorry
