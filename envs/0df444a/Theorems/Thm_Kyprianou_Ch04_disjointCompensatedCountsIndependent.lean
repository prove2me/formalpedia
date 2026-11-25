-- Prove2me | Theorems.Thm_Kyprianou_Ch04_disjointCompensatedCountsIndependent
-- name    : Kyprianou.Ch04.disjointCompensatedCountsIndependent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:37:26.573221+00:00
-- url     : https://prove2.me/theorems/03f5e0b9-6bd9-4b9f-ae11-901a7abccfb0
-- title:
--   Compensated counts on disjoint marked-time sets are independent
-- statement:
--   Composition of independent Poisson counts with the measurable deterministic compensation map preserves independence.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4: disjoint compensated Poisson increments.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Theorems.Thm_Kyprianou_Ch04_disjointPoissonCountsIndependent
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.disjointCompensatedCountsIndependent
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hdisj : Disjoint B B') :
    IndepFun (fun ω => N.compensated B ω) (fun ω => N.compensated B' ω) P := by
  sorry
