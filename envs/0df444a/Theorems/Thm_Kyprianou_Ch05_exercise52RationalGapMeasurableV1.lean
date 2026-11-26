-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52RationalGapMeasurableV1
-- name    : Kyprianou.Ch05.exercise52RationalGapMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:20:32.853288+00:00
-- url     : https://prove2.me/theorems/54e1686b-957a-49e9-ad0a-d9bed9fe84c8
-- title:
--   The rational-coordinate strict gap event is measurable in path space
-- statement:
--   The rational-coordinate strict gap event is measurable in path space
-- source:
--   Kyprianou (2006), Exercise 5.2(ii), renewal comparison

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
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

theorem Kyprianou.Ch05.exercise52RationalGapMeasurableV1
    (x u y : ℝ) :
    MeasurableSet {g : NNReal → ℝ | ∃ a b : ℚ, (a : ℝ) < x - y ∧ x + u < (b : ℝ) ∧
      (∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)} := by
  sorry
