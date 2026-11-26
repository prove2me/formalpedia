-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RawCompoundDownJumpV5
-- name    : Kyprianou.Ch04.exercise49RawCompoundDownJumpV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:07:30.859028+00:00
-- url     : https://prove2.me/theorems/3ebecb14-125d-53a1-a4a0-fe44f0c717a0
-- title:
--   exercise49RawCompoundDownJumpV5
-- statement:
--   exercise49RawCompoundDownJumpV5
-- source:
--   Exercise 4.9(iii): admissible model construction

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RawCompoundDownJumpV5
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : NNReal)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (b : ℝ) (hb : 0 < b) :
    ∀ᵐ w ∂P, ¬ Monotone (fun t : NNReal =>
      LevyFoundations.compoundPoisson b τ Y (t : ℝ) w) := by
  sorry
