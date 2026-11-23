-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonLocallyFiniteStepRepresentationV1
-- name    : Kyprianou.Ch02.finiteRegionPoissonLocallyFiniteStepRepresentationV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:45:45.540235+00:00
-- url     : https://prove2.me/theorems/d17f62e1-b633-4f68-826e-8975dd391109
-- title:
--   Finite-support Poisson integrals have locally finite marked-step representations on all bounded horizons
-- statement:
--   For each sample in the probability-one finite-support event and each integer horizon T, the stopped marked Poisson integral is a finite linear combination of right-continuous step indicators of its space-time atoms, uniformly for t≤T. The finite weights capture the actual integral, including its Bochner integrability convention. This is the remaining measure-theoretic bridge from finite atomic support to càdlàg paths of the original Poisson random measure.
-- source:
--   Kyprianou (2006), Lemma 2.8, local step representation under finite activity, target 805711a8-430a-4fe5-8eed-4ff947ba6151, Chapter 2 mission Eq. (2.3).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteRegionPoissonLocallyFiniteStepRepresentationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hSupport : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ (s : Finset (ℝ × ℝ))
      (weight : ℝ × ℝ → ℝ), ∀ t : ℝ≥0, t ≤ (T : ℝ≥0) →
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) =
        ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0 := by sorry
