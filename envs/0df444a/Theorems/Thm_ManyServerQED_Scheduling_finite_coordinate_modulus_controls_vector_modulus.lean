-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_finite_coordinate_modulus_controls_vector_modulus
-- name    : ManyServerQED.Scheduling.finite_coordinate_modulus_controls_vector_modulus
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:55:47.231239+00:00
-- url     : https://prove2.me/theorems/4946a128-0e61-45d5-9fbb-edff55391ca8
-- title:
--   Finite coordinate moduli control the vector modulus
-- statement:
--   An asymptotically small uniform modulus in probability for each coordinate of a finite vector process implies the same bound for the vector-valued process with the maximum norm.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory
open scoped ENNReal

theorem ManyServerQED.Scheduling.finite_coordinate_modulus_controls_vector_modulus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (T : ℝ)
    (h : ∀ i : Fin k, ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
        ε ≤ |X n ω s i-X n ω t i|} ≤ ENNReal.ofReal η) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η := by sorry
