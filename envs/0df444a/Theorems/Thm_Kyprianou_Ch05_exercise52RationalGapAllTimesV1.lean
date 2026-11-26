-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52RationalGapAllTimesV1
-- name    : Kyprianou.Ch05.exercise52RationalGapAllTimesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:23:05.288512+00:00
-- url     : https://prove2.me/theorems/38874d0f-13c5-4d15-845c-54b229b97b37
-- title:
--   A right-continuous path avoids a real open interval iff its rational samples avoid it
-- statement:
--   A right-continuous path avoids a real open interval iff its rational samples avoid it
-- source:
--   Kyprianou (2006), Exercise 5.2(ii)

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

theorem Kyprianou.Ch05.exercise52RationalGapAllTimesV1
    (Y : NNReal → ℝ) (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (a b : ℝ) :
    (∀ t : NNReal, Y t ≤ a ∨ b ≤ Y t) ↔
      (∀ q : ℚ, Y (Real.toNNReal q) ≤ a ∨ b ≤ Y (Real.toNNReal q)) := by
  sorry
