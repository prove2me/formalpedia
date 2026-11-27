-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridPairFromSingleErrorV1
-- name    : Kyprianou.Ch04.gridPairFromSingleErrorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:33:38.093165+00:00
-- url     : https://prove2.me/theorems/1e6cdb06-13e8-5fca-8409-36641129d925
-- title:
--   gridPairFromSingleErrorV1
-- statement:
--   A uniform single-cutoff grid comparison to a common reference implies the cofinal pairwise comparison.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A mesh-uniform one-cutoff probability estimate implies its cofinal two-cutoff version. -/

theorem Kyprianou.Ch04.gridPairFromSingleErrorV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : NNReal)
    (A : ℕ → NNReal → Ω → ℝ) (B : ℕ → ℕ → NNReal → Ω → ℝ)
    (h : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, (P {w | ∃ t ≤ T, δ ≤ |B m n t w-A n t w|}).toReal ≤ η) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T,
        δ ≤ |B l n t w-B m n t w|}).toReal ≤ η := by
  sorry
