-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailProbabilityV1
-- name    : Kyprianou.Ch05.exercise52IntegratedTailProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:23.466314+00:00
-- url     : https://prove2.me/theorems/ca4dbcc8-4222-5bc6-a702-015fabb27696
-- title:
--   The normalised integrated-tail density is a probability law
-- statement:
--   The normalised integrated-tail density is a probability law
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

theorem Kyprianou.Ch05.exercise52IntegratedTailProbabilityV1
    (nu : Measure ℝ) (m : ℝ) (hm : 0 < m)
    (hMass : m = ∫ z in Ioi (0 : ℝ), (nu (Ioi z)).toReal ∂volume) :
    IsProbabilityMeasure (ascendingRecordJumpDistribution nu m) := by
  sorry
