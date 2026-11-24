-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmIntegrableMarkCompensatedSetIntegralV1
-- name    : Kyprianou.Ch02.prmIntegrableMarkCompensatedSetIntegralV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T22:33:06.233646+00:00
-- url     : https://prove2.me/theorems/ed17450f-4e22-49da-bc68-321c2f5e1f51
-- title:
--   Integrable deterministic compensated Poisson marks: preservation of integrals over every completed-past event
-- statement:
--   Show the future increment is centred on every completed-past event. First for raw natural past events use independence of future finite-intensity counts, extend to nonnegative mark integrals via the mean measure on the event, and use signed integrability. For the completed right-continuous past approximate an event at a strictly later raw time and let that time decrease to the conditioning time with the L1 Campbell gap bound. Add the adjacent-window integrals using a.s. sample integrability.
-- source:
--   Kyprianou (2006), Chapter 2 Exercise 2.6(ii) and Lemma 2.9; source-exact child of cf1997aa-ddd2-409a-b6cd-4c701c281c95.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmIntegrableMarkCompensatedSetIntegralV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ), f z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x, f x ∂ν
    ∀ (s t : ℝ≥0), s ≤ t → ∀ E : Set Ω,
      @MeasurableSet Ω (ℱ s) E →
      (∫ ω in E, M s ω ∂P) = (∫ ω in E, M t ω ∂P) := by sorry

end Kyprianou.Ch02
