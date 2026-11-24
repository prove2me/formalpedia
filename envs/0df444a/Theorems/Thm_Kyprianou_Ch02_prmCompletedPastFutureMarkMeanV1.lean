-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmCompletedPastFutureMarkMeanV1
-- name    : Kyprianou.Ch02.prmCompletedPastFutureMarkMeanV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:39:11.234486+00:00
-- url     : https://prove2.me/theorems/fa4205d6-d62d-4a5e-8378-b09d4fe9a977
-- title:
--   Real integrable marked Poisson future integral has the correct expectation on every completed-past event
-- statement:
--   Push the restricted time-window random measure forward by the mark projection. Its mean measure under P restricted to E equals the scalar multiple of ν by the completed-past count identity; then apply the real bind integral formula.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9 and Exercise 2.6(ii); conditional mean of Poisson mark increments.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmCompletedPastFutureMarkMeanV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    (s t : ℝ≥0) (hst : s ≤ t) (E : Set Ω) (hE : @MeasurableSet Ω (ℱ s) E)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f ν) :
    ∫ ω in E, (∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ), f z.2 ∂(N.N ω)) ∂P =
      P.real E * (((t : ℝ) - (s : ℝ)) * ∫ x, f x ∂ν) := by sorry

end Kyprianou.Ch02
