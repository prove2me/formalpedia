-- Prove2me | Theorems.Thm_Kyprianou_Ch04_normalisedGridProbabilityTransferV1
-- name    : Kyprianou.Ch04.normalisedGridProbabilityTransferV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:26:17.392887+00:00
-- url     : https://prove2.me/theorems/439456d2-af6d-52e3-b464-e89a69551f59
-- title:
--   normalisedGridProbabilityTransferV1
-- statement:
--   Pairwise uniform grid probability bound transfers to the fixed-mesh limit, with the initial cell restored.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_outerProbabilityLiminfBoundV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform pairwise grid estimates pass to the fixed-mesh path limit, then the
vanishing initial-cell error is restored by the outer-probability union bound. -/

theorem Kyprianou.Ch04.normalisedGridProbabilityTransferV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : NNReal)
    (A : ℕ → NNReal → Ω → ℝ) (B I R : ℕ → ℕ → NNReal → Ω → ℝ)
    (hR : ∀ m n t w, R m n t w = (A n t w - B m n t w) + I m n t w)
    (hp : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, ∀ᶠ l in atTop, (P {w | ∃ t ≤ T,
        δ ≤ |B l n t w - B m n t w|}).toReal ≤ η)
    (hl : ∀ᵐ w ∂P, ∀ n, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ l ≥ N,
      ∀ t ≤ T, |B l n t w - A n t w| < δ)
    (hi : ∀ m, ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (P {w | ∃ t ≤ T, δ ≤ |I m n t w|}).toReal ≤ η) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop, ∀ᶠ n in atTop,
      (P {w | ∃ t ≤ T, δ ≤ |R m n t w|}).toReal ≤ η := by
  sorry
