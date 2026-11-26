-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49UniformDriverCountBoundV5
-- name    : Kyprianou.Ch04.exercise49UniformDriverCountBoundV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:07:37.515924+00:00
-- url     : https://prove2.me/theorems/48d6a1a0-640e-4871-a616-5383fed53e99
-- title:
--   exercise49UniformDriverCountBoundV5
-- statement:
--   exercise49UniformDriverCountBoundV5
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

theorem Kyprianou.Ch04.exercise49UniformDriverCountBoundV5
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : NNReal)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ w ∂P, ∃ N : ℕ, ∀ t ≥ 0,
      (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n w) t : ℝ) ≤ N + t / c := by
  sorry
