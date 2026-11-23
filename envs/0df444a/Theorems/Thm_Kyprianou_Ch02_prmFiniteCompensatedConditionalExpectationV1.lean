-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteCompensatedConditionalExpectationV1
-- name    : Kyprianou.Ch02.prmFiniteCompensatedConditionalExpectationV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:04:10.745801+00:00
-- url     : https://prove2.me/theorems/e540904b-a0e1-4539-a218-94f06bca7cae
-- title:
--   Conditional-expectation centring of finite-region compensated KLS Poisson increments
-- statement:
--   Conditional expectation of the compensated Poisson marked integral at future time t given the completed natural Poisson filtration at time s is equal almost everywhere to the compensated integral at s, for s ≤ t. Requires future-past independence under the right-continuously completed filtration and zero-mean marked increments.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.9 general finite-region compensated martingale, KLS natural completed filtration and proved LeanLevy martingale proof

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteCompensatedConditionalExpectationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    ∀ (s t : ℝ≥0), s ≤ t →
      P[((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t) | ℱ s] =ᵐ[P]
        ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) s) := by sorry
