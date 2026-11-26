-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_measurable_polygonal_approximation_on_unit_interval
-- name    : ManyServerQED.Scheduling.measurable_polygonal_approximation_on_unit_interval
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:13:18.349187+00:00
-- url     : https://prove2.me/theorems/8ec8f5f0-4e78-4883-b462-304cfb710c6c
-- title:
--   Measurable polygonal approximation on the unit interval
-- statement:
--   From measurable evaluations of a finite-vector process on the unit interval, construct its measurable piecewise linear interpolant on the uniform grid. The interpolant preserves a uniform norm bound, and its error is bounded by the original process modulus at one mesh length.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory Finset
open scoped NNReal ENNReal

theorem ManyServerQED.Scheduling.measurable_polygonal_approximation_on_unit_interval {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    [MeasurableSpace C(Icc (0:ℝ) 1, Fin k → ℝ)] [BorelSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    (m : ℕ)
    (X : Ω → ℝ → Fin k → ℝ)
    (hXm : ∀ t ∈ Icc (0:ℝ) 1, Measurable (fun ω => X ω t)) :
    ∃ Y : Ω → C(Icc (0:ℝ) 1,Fin k → ℝ), Measurable Y ∧
      (∀ ω (A : ℝ), (∀ t ∈ Icc (0:ℝ) 1, ‖X ω t‖ ≤ A) → ∀ s, ‖Y ω s‖ ≤ A) ∧
      ∀ ω (e : ℝ), (∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t| ≤ 1/(m+1:ℕ) →
        ‖X ω s-X ω t‖ ≤ e) →
        ∀ s : Icc (0:ℝ) 1, ‖Y ω s-X ω s‖ ≤ e := by sorry
