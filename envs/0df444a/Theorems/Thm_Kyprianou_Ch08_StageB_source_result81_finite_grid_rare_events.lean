-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_grid_rare_events
-- name    : Kyprianou.Ch08.StageB.source_result81_finite_grid_rare_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:07:58.608527+00:00
-- url     : https://prove2.me/theorems/fa77a732-cd9f-4f0e-b7e8-088bf3242645
-- title:
--   Vanishing finite grid probabilities exclude eventual bad cells
-- statement:
--   If every grid cell has probability at most b(n) and the grid count times b(n) tends to zero, then for every integer multiple of the grid count, almost surely it is false that some included cell is bad at every sufficiently late index.
-- source:
--   Finite-union and measure-zero step for Kyprianou (2006), Chapter 8, Theorem 8.1. Parent Prove2Me theorem 92200ffc-acdc-4836-b709-dd420298cdde.

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_finite_grid_rare_events
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → ℕ → Set Ω) (cnt : ℕ → ℕ) (b : ℕ → ℝ)
    (hlim : Tendsto (fun n => (cnt n : ℝ) * b n) atTop (𝓝 0))
    (hE : ∀ n k, P (E n k) ≤ ENNReal.ofReal (b n)) :
    ∀ᵐ ω ∂P, ∀ M : ℕ, ¬ (∀ᶠ n in atTop, ∃ k < M * cnt n, ω ∈ E n k) := by
  sorry
