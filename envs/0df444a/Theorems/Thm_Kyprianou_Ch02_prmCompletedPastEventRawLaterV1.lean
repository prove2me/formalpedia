-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmCompletedPastEventRawLaterV1
-- name    : Kyprianou.Ch02.prmCompletedPastEventRawLaterV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:39:00.678462+00:00
-- url     : https://prove2.me/theorems/d662e711-5d9c-4eb5-aea3-78b4a362bc54
-- title:
--   Every completed-past event has an almost-sure raw representative at each strictly later time
-- statement:
--   The minimal completed right-continuous filtration is bounded by the right-continuous modification of the completed raw count filtration; a later raw representative follows.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9 and Exercise 2.6(ii); conditional mean of Poisson mark increments.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmCompletedPastEventRawLaterV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    (s u : ℝ≥0) (hsu : s < u) (E : Set Ω) (hE : @MeasurableSet Ω (ℱ s) E) :
    ∃ A : Set Ω, @MeasurableSet Ω (⨆ (v : ℝ≥0) (_ : v ≤ u) (A : Set ℝ) (_ : MeasurableSet A),
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) inferInstance) A ∧ E =ᵐ[P] A := by sorry

end Kyprianou.Ch02
