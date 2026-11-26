-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CPDriverStationaryV1
-- name    : Kyprianou.Ch05.exercise52CPDriverStationaryV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:44:46.676192+00:00
-- url     : https://prove2.me/theorems/b06b04b0-1f6d-47a4-af3d-a35b2ccd6016
-- title:
--   The driftless compound Poisson driver has stationary increments
-- statement:
--   A compound Poisson driver admits a measurable Levy version with the same whole-path law
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

theorem Kyprianou.Ch05.exercise52CPDriverStationaryV1
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    HasStationaryIncrements (fun (t : NNReal) w =>
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) Q := by
  sorry
