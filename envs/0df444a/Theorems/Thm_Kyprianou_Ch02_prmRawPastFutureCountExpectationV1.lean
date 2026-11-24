-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmRawPastFutureCountExpectationV1
-- name    : Kyprianou.Ch02.prmRawPastFutureCountExpectationV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:38:56.349918+00:00
-- url     : https://prove2.me/theorems/1606d2f5-0f41-43ad-b3cb-105d09cfc590
-- title:
--   Poisson count expectation restricted to a raw natural-past event
-- statement:
--   For finite mark intensity the joint past-future independence yields the product of the event probability and the Poisson mean. For infinite intensity use the almost-sure infinite-count property.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9 and Exercise 2.6(ii); conditional mean of Poisson mark increments.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmRawPastFutureCountExpectationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (u t : ℝ≥0) (hut : u < t) (C : Set ℝ) (hC : MeasurableSet C)
    (E : Set Ω) (hE : @MeasurableSet Ω (⨆ (v : ℝ≥0) (_ : v ≤ u) (A : Set ℝ) (_ : MeasurableSet A),
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) inferInstance) E) :
    ∫⁻ ω in E, N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C) ∂P =
      P E * (ENNReal.ofReal ((t : ℝ) - (u : ℝ)) * ν C) := by sorry

end Kyprianou.Ch02
