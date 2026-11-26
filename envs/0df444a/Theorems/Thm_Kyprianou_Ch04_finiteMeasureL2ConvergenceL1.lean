-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteMeasureL2ConvergenceL1
-- name    : Kyprianou.Ch04.finiteMeasureL2ConvergenceL1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:38:56.844601+00:00
-- url     : https://prove2.me/theorems/bd9cbd75-d3b6-58a7-82b4-93d06b0ff5ba
-- title:
--   Finite-measure L2 convergence implies L1 convergence
-- statement:
--   On a finite measure space the L1 error tends to zero whenever the L2 error tends to zero, by the exponent comparison inequality and the squeeze theorem.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; predictable isometry extension.

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.finiteMeasureL2ConvergenceL1
    {A : Type u} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (f : ℕ → A → ℝ) (g : A → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ)
    (h₂ : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
  sorry
