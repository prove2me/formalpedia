-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compensatedCrossDisjointZero
-- name    : Kyprianou.Ch04.compensatedCrossDisjointZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:31:56.972195+00:00
-- url     : https://prove2.me/theorems/592edaf4-be21-45d3-a5e3-548f5a84ccab
-- title:
--   Disjoint compensated Poisson boxes have zero cross-moment
-- statement:
--   Let N be a Poisson random measure with reference intensity. For two disjoint measurable time-mark sets, the compensated masses are independent. If the first set has finite intensity, their product has zero expected value. No finite intensity of the second is needed for mean centring of the first.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4: disjoint compensated Poisson covariance; adapted from the original LevyStochCalc source proof.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.compensatedCrossDisjointZero
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hdisj : Disjoint B B') :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P = 0 := by
  sorry
