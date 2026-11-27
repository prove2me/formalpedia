-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridResidualTriangleTransferV1
-- name    : Kyprianou.Ch04.gridResidualTriangleTransferV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:02:04.935905+00:00
-- url     : https://prove2.me/theorems/0ca00b19-0b47-41f5-88db-43a40f1dacd9
-- title:
--   gridResidualTriangleTransferV1
-- statement:
--   gridResidualTriangleTransferV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), outer probability error transfer

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Choose one common cutoff for the two cofinal error estimates. -/

theorem Kyprianou.Ch04.gridResidualTriangleTransferV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : NNReal) (A : ℕ → ℕ → NNReal → Ω → ℝ) (B : ℕ → NNReal → Ω → ℝ)
    (R : ℕ → ℕ → NNReal → Ω → ℝ)
    (hR : ∀ m n t w, R m n t w = A m n t w + B m t w)
    (hA : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, δ ≤ |A m n t w|}).toReal ≤ η)
    (hB : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      (P {w | ∃ t ≤ T, δ ≤ |B m t w|}).toReal ≤ η) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, δ ≤ |R m n t w|}).toReal ≤ η := by
  sorry
