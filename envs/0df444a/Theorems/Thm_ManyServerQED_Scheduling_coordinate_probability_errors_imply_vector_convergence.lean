-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_coordinate_probability_errors_imply_vector_convergence
-- name    : ManyServerQED.Scheduling.coordinate_probability_errors_imply_vector_convergence
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:00:34.458049+00:00
-- url     : https://prove2.me/theorems/1c07afdb-1351-5939-9663-e9b1c0faaec9
-- title:
--   Coordinate errors imply convergence in probability of finite vectors
-- statement:
--   If every coordinate of a sequence of finite-dimensional real random vectors tends to zero in probability, then the vectors tend to zero in probability.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Finset

theorem ManyServerQED.Scheduling.coordinate_probability_errors_imply_vector_convergence {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {I : Type*} [Fintype I] (D : ℕ → Ω → I → ℝ)
    (h : ∀ i ε, 0 < ε → Tendsto (fun n => P {ω | ε ≤ |D n ω i|}) atTop (𝓝 0)) :
    TendstoInMeasure P D atTop (fun _ => 0) := by sorry
