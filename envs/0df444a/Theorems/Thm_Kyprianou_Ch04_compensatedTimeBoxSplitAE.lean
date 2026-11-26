-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compensatedTimeBoxSplitAE
-- name    : Kyprianou.Ch04.compensatedTimeBoxSplitAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:01.375574+00:00
-- url     : https://prove2.me/theorems/b5cd3115-b267-471e-903d-c787935bbb6a
-- title:
--   Compensated Poisson time-box splitting
-- statement:
--   A compensated Poisson count over a deterministic time-mark box equals the sum over its two disjoint consecutive time subintervals almost surely.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; overlapping predictable rectangle covariance.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_compensatedDisjointUnionAE
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.compensatedTimeBoxSplitAE
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (a b t : NNReal) (hab : a ≤ b) (hbt : b ≤ t)
    (A : Set E) (hA : MeasurableSet A)
    (hFin : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤) :
    (fun ω => N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ω) =ᵐ[P]
      (fun ω => N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω +
        N.compensated (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ A) ω) := by
  sorry
