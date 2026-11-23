-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteCompensatedStronglyAdaptedIntegrableV1
-- name    : Kyprianou.Ch02.prmFiniteCompensatedStronglyAdaptedIntegrableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:04:19.01384+00:00
-- url     : https://prove2.me/theorems/46db8b2a-c2bc-417e-98a5-e062c7fbd367
-- title:
--   Adaptedness and integrability of finite-region compensated KLS Poisson process
-- statement:
--   Show that the finite-intensity signed marked Poisson integral is strongly measurable in the completed natural filtration at each time, and integrable. Reuse the measurable Poisson integral approximation and first-moment identities.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.9 general finite-region compensated martingale, KLS natural completed filtration and proved LeanLevy martingale proof

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteCompensatedStronglyAdaptedIntegrableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    (∀ t : ℝ≥0, StronglyMeasurable[ℱ t] ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t)) ∧
    (∀ t : ℝ≥0, Integrable ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t) P) := by sorry
