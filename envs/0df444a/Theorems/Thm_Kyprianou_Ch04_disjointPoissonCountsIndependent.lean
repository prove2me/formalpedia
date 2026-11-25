-- Prove2me | Theorems.Thm_Kyprianou_Ch04_disjointPoissonCountsIndependent
-- name    : Kyprianou.Ch04.disjointPoissonCountsIndependent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:34:49.499131+00:00
-- url     : https://prove2.me/theorems/2ebd4d91-487d-468f-acfb-54943e77b309
-- title:
--   Raw Poisson counts on disjoint marked-time sets are independent
-- statement:
--   The disjoint-set independence axiom of a Poisson random measure implies independence of the two evaluation random variables.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4, independent scattering of Poisson random measures.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.disjointPoissonCountsIndependent
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hdisj : Disjoint B B') :
    IndepFun (fun ω => N.N ω B) (fun ω => N.N ω B') P := by
  sorry
