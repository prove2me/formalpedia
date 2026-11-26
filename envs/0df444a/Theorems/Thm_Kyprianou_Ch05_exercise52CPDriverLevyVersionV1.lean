-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CPDriverLevyVersionV1
-- name    : Kyprianou.Ch05.exercise52CPDriverLevyVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:41:46.952624+00:00
-- url     : https://prove2.me/theorems/930cf186-bae2-4819-a47f-70b78d2a1610
-- title:
--   A compound Poisson driver admits a measurable Levy version with the same whole-path law
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

theorem Kyprianou.Ch05.exercise52CPDriverLevyVersionV1
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    ∃ Z : NNReal → Lambda → ℝ, IsLevyProcess Z Q ∧
      (∀ t, Measurable (Z t)) ∧
      (∀ᵐ w ∂Q, ∀ t : NNReal, Z t w =
        ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) := by
  sorry
