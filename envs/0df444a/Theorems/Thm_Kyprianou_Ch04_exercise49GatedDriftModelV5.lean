-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49GatedDriftModelV5
-- name    : Kyprianou.Ch04.exercise49GatedDriftModelV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:09:47.699745+00:00
-- url     : https://prove2.me/theorems/5622d7ed-5e64-4b3f-a3da-8de23ca89031
-- title:
--   exercise49GatedDriftModelV5
-- statement:
--   exercise49GatedDriftModelV5
-- source:
--   Exercise 4.9(iii): unconditional counterexample

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49GatedDriftModelV5
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : NNReal)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (b : ℝ) :
    ∃ X : NNReal → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ,
      IsLevyProcess X P ∧ ∀ᵐ w ∂P, ∀ t : NNReal,
        X t w = LevyFoundations.compoundPoisson b τ Y (t : ℝ) w := by
  sorry
