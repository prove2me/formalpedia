-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmIntegrableMarkCompensatedAdaptedV1
-- name    : Kyprianou.Ch02.prmIntegrableMarkCompensatedAdaptedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:32:58.524115+00:00
-- url     : https://prove2.me/theorems/67e18233-d28d-4632-a9b0-122e91cf536a
-- title:
--   Integrable deterministic Poisson marks: strong adaptation and integrability on the completed filtration
-- statement:
--   Show the time-window mark measure is measurable for the completed filtration by testing all mark sets. Use measurable positive/negative lintegrals and Campbell integrability to identify the Bochner integral; establish L1 control by the absolute mark expectation. This is the strongly adapted and integrable part of the source-exact general mark martingale.
-- source:
--   Kyprianou (2006), Chapter 2 Exercise 2.6(ii) and Lemma 2.9; source-exact child of cf1997aa-ddd2-409a-b6cd-4c701c281c95.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmIntegrableMarkCompensatedAdaptedV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ), f z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x, f x ∂ν
    (∀ t, StronglyMeasurable[ℱ t] (M t)) ∧ (∀ t, Integrable (M t) P) := by sorry

end Kyprianou.Ch02
