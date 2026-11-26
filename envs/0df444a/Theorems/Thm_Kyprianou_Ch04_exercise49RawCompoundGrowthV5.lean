-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RawCompoundGrowthV5
-- name    : Kyprianou.Ch04.exercise49RawCompoundGrowthV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:07:35.227064+00:00
-- url     : https://prove2.me/theorems/27933741-0978-42e0-9938-5c9068521ba5
-- title:
--   exercise49RawCompoundGrowthV5
-- statement:
--   exercise49RawCompoundGrowthV5
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

theorem Kyprianou.Ch04.exercise49RawCompoundGrowthV5
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : NNReal)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (c : ℝ) (hc : 0 < c)
    (hCount : ∀ᵐ w ∂P, ∃ N : ℕ, ∀ t ≥ 0,
      (LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n w) t : ℝ) ≤ N + t / c) :
    ∀ᵐ w ∂P, Tendsto (fun t : NNReal =>
      LevyFoundations.compoundPoisson (1 + 1 / c) τ Y (t : ℝ) w) atTop atTop := by
  sorry
