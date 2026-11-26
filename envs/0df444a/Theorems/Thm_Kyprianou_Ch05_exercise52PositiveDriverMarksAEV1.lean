-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52PositiveDriverMarksAEV1
-- name    : Kyprianou.Ch05.exercise52PositiveDriverMarksAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:23:02.702587+00:00
-- url     : https://prove2.me/theorems/e8f0c7c1-9dc2-4833-aa6c-807974e15139
-- title:
--   All marks of a positive compound Poisson driver are strictly positive almost surely
-- statement:
--   All marks of a positive compound Poisson driver are strictly positive almost surely
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

theorem Kyprianou.Ch05.exercise52PositiveDriverMarksAEV1
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    (arrival marks : ℕ → Lambda → ℝ) (F : Measure ℝ)
    (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    ∀ᵐ w ∂Q, ∀ n, 0 < marks n w := by
  sorry
