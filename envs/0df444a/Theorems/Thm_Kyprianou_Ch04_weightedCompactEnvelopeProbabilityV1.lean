-- Prove2me | Theorems.Thm_Kyprianou_Ch04_weightedCompactEnvelopeProbabilityV1
-- name    : Kyprianou.Ch04.weightedCompactEnvelopeProbabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:12:56.83614+00:00
-- url     : https://prove2.me/theorems/91765560-685b-5f30-bebf-1897de127dbb
-- title:
--   weightedCompactEnvelopeProbabilityV1
-- statement:
--   weightedCompactEnvelopeProbabilityV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_outerAEEventTailV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite pathwise variation may multiply a vanishing measurable error envelope
without requiring an integrable variation bound. -/

theorem Kyprianou.Ch04.weightedCompactEnvelopeProbabilityV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (C : Ω → ℝ) (D E : ℕ → Ω → ℝ≥0∞)
    (hC : Measurable C) (hD : ∀ m, Measurable (D m))
    (hE : ∀ m, Measurable (E m))
    (hb : ∀ᵐ w ∂P, 0 ≤ C w ∧ ∀ m, D m w ≠ ⊤ → E m w ≠ ⊤ →
      ∀ t ≤ T, |R m t w| ≤ C w * (D m w).toReal + (E m w).toReal)
    (hc : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ m ≥ N,
      D m w ≤ ENNReal.ofReal d ∧ E m w ≤ ENNReal.ofReal d)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun m => (P {w | ∃ t ≤ T, δ ≤ |R m t w|}).toReal) atTop (nhds 0) := by
  sorry
