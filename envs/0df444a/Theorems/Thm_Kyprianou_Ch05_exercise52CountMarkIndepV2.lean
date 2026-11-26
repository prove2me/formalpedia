-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CountMarkIndepV2
-- name    : Kyprianou.Ch05.exercise52CountMarkIndepV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:44:51.128804+00:00
-- url     : https://prove2.me/theorems/c6918603-e67d-4852-ab62-0defc5252ad3
-- title:
--   The arrival count is measurable and independent of the entire mark sequence
-- statement:
--   The arrival count is measurable and independent of the entire mark sequence
-- source:
--   Kyprianou (2006), Exercise 5.2(ii)

import Mathlib
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_arrival
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

theorem Kyprianou.Ch05.exercise52CountMarkIndepV2
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) (t : NNReal) :
    let N := fun w => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival arrival n w) (t : ℝ)
    Measurable N ∧ IndepFun N (fun w n => marks n w) Q := by
  sorry
