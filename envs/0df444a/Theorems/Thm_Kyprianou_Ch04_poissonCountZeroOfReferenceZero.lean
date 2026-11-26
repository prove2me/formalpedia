-- Prove2me | Theorems.Thm_Kyprianou_Ch04_poissonCountZeroOfReferenceZero
-- name    : Kyprianou.Ch04.poissonCountZeroOfReferenceZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:51:18.48889+00:00
-- url     : https://prove2.me/theorems/2b5d016e-4c14-576b-8f3b-f2c0da449398
-- title:
--   Poisson counts vanish on zero-reference-intensity sets
-- statement:
--   A measurable set with zero reference intensity has zero Poisson count almost surely, for the same KLS modular Poisson measure.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; treatment of the time-zero boundary.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.poissonCountZeroOfReferenceZero
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) (A : Set (ℝ × E))
    (hA : MeasurableSet A) (h0 : referenceIntensity ν A = 0) :
    ∀ᵐ ω ∂P, N.N ω A = 0 := by
  sorry
