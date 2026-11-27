-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridUniformWeightedEnvelopeProbabilityV1
-- name    : Kyprianou.Ch04.gridUniformWeightedEnvelopeProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:33:37.481005+00:00
-- url     : https://prove2.me/theorems/5f27c4d8-c212-5417-ae64-900557ee8eab
-- title:
--   gridUniformWeightedEnvelopeProbabilityV1
-- statement:
--   A finite random variation factor and a vanishing measurable state envelope yield a uniform bound over all grid meshes.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A measurable vanishing error envelope times finite samplewise variation
controls every mesh simultaneously in outer probability. -/

theorem Kyprianou.Ch04.gridUniformWeightedEnvelopeProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : ℕ → ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (C : Ω → ℝ) (D : ℕ → Ω → ℝ≥0∞)
    (hC : Measurable C) (hD : ∀ m, Measurable (D m))
    (hb : ∀ᵐ w ∂P, 0 ≤ C w ∧ ∀ m, D m w ≠ ⊤ →
      ∀ n t, t ≤ T → |R m n t w| ≤ C w * (D m w).toReal)
    (hc : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ m ≥ N,
      D m w ≤ ENNReal.ofReal d) :
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop,
      ∀ n, (P {w | ∃ t ≤ T, δ ≤ |R m n t w|}).toReal ≤ η := by
  sorry
