-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmCompletedPastFutureCountExpectationV1
-- name    : Kyprianou.Ch02.prmCompletedPastFutureCountExpectationV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:39:02.610157+00:00
-- url     : https://prove2.me/theorems/46349cfb-d876-42fd-a0e7-1f53d5e9fe95
-- title:
--   Poisson future count mean on any completed natural-past event
-- statement:
--   Approximate the left time endpoint from above by a decreasing sequence. Each later raw representative of E has the same restricted measure; use the raw future expectation and continuity from below of the counts and their nonnegative integrals. The zero-window case is immediate.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9 and Exercise 2.6(ii); conditional mean of Poisson mark increments.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmCompletedPastFutureCountExpectationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    (s t : ℝ≥0) (hst : s ≤ t) (C : Set ℝ) (hC : MeasurableSet C)
    (E : Set Ω) (hE : @MeasurableSet Ω (ℱ s) E) :
    ∫⁻ ω in E, N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ C) ∂P =
      P E * (ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * ν C) := by sorry

end Kyprianou.Ch02
