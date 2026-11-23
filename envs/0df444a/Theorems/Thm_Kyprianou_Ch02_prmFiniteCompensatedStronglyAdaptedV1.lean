-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteCompensatedStronglyAdaptedV1
-- name    : Kyprianou.Ch02.prmFiniteCompensatedStronglyAdaptedV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:25:00.993842+00:00
-- url     : https://prove2.me/theorems/815d2207-e37e-498c-bc18-2e4c41cbf06f
-- title:
--   Strong adaptedness of the finite-region compensated KLS Poisson process
-- statement:
--   Strong measurability of each finite-region compensated Poisson integral at the completed natural-filtration time. Prove by the KLS local-evaluation sigma measurability theorem and filtration admissibility.
-- source:
--   Kyprianou (2006) Chapter 2, Lemma 2.9, finite-band compensated Poisson martingale

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteCompensatedStronglyAdaptedV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    ∀ t : ℝ≥0, StronglyMeasurable[ℱ t] ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t) := by sorry
