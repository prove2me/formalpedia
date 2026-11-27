-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridPairErrorUnionV1
-- name    : Kyprianou.Ch04.gridPairErrorUnionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:32:18.214065+00:00
-- url     : https://prove2.me/theorems/c598935a-b9ad-52e5-9737-f7060b6fd578
-- title:
--   gridPairErrorUnionV1
-- statement:
--   The cofinal finite-variation and small-jump grid probability estimates combine by the union bound.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Cofinal probability bounds for the finite-variation and martingale parts
combine without assuming the deviation events themselves are measurable. -/

theorem Kyprianou.Ch04.gridPairErrorUnionV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : NNReal) (A B R : ℕ → ℕ → ℕ → NNReal → Ω → ℝ)
    (hR : ∀ m n l t w, R m n l t w = A m n l t w+B m n l t w)
    (hA : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T, δ ≤ |A m n l t w|}).toReal ≤ η)
    (hB : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T, δ ≤ |B m n l t w|}).toReal ≤ η) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T, δ ≤ |R m n l t w|}).toReal ≤ η := by
  sorry
