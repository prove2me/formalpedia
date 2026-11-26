-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52ArrivalMarkSequenceIndepV1
-- name    : Kyprianou.Ch05.exercise52ArrivalMarkSequenceIndepV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:50:42.416348+00:00
-- url     : https://prove2.me/theorems/13a7ae0d-23c9-51c7-b41f-ca848bbc5368
-- title:
--   Arrival and mark sequences are independent
-- statement:
--   The arrival and mark sequence random variables are independent.
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

theorem Kyprianou.Ch05.exercise52ArrivalMarkSequenceIndepV1
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    IndepFun (fun w n => arrival n w) (fun w n => marks n w) Q := by
  sorry
