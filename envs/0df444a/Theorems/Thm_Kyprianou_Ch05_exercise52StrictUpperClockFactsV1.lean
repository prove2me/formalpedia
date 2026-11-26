-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52StrictUpperClockFactsV1
-- name    : Kyprianou.Ch05.exercise52StrictUpperClockFactsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:22:49.811134+00:00
-- url     : https://prove2.me/theorems/f7c3d361-9bce-5cfe-90bd-29d22a3ba8fe
-- title:
--   A finite strict upper crossing of a positive barrier has positive time and reaches at least the barrier
-- statement:
--   A finite strict upper crossing of a positive barrier has positive time and reaches at least the barrier
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

theorem Kyprianou.Ch05.exercise52StrictUpperClockFactsV1
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (x : ℝ) (hx : 0 < x) (s : NNReal)
    (hs : (s : WithTop NNReal) = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ x < Y t}) :
    0 < s ∧ (∀ t : NNReal, t < s → Y t ≤ x) ∧ x ≤ Y s := by
  sorry
