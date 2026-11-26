-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CPRenewalGapEventAEV1
-- name    : Kyprianou.Ch05.exercise52CPRenewalGapEventAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:20:38.983745+00:00
-- url     : https://prove2.me/theorems/f38f7335-4567-41af-b9b8-8e80b1e6aece
-- title:
--   The canonical compound Poisson rational gap event equals its embedded renewal passage event
-- statement:
--   The canonical compound Poisson rational gap event equals its embedded renewal passage event
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

theorem Kyprianou.Ch05.exercise52CPRenewalGapEventAEV1
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    ∀ᵐ w ∂Q, (u < renewalOvershoot marks x w ∧ y < renewalUndershoot marks x w) ↔
      (fun (t : NNReal) => ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) ∈ {g : NNReal → ℝ | ∃ a b : ℚ, (a : ℝ) < x - y ∧ x + u < (b : ℝ) ∧
      (∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)} := by
  sorry
