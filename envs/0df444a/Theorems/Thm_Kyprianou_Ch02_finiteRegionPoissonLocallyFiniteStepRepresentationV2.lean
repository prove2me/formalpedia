-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonLocallyFiniteStepRepresentationV2
-- name    : Kyprianou.Ch02.finiteRegionPoissonLocallyFiniteStepRepresentationV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:53:35.704317+00:00
-- url     : https://prove2.me/theorems/1510bc05-e07a-421f-87e9-149f8f04853b
-- title:
--   Finite-region Poisson local marked-step representation, validated KLS source interface
-- statement:
--   The existing Chapter 2 local finite-step representation theorem with exactly the same source statement, but a minimal KLS Atomic Definition provider matching other remotely accepted theorem records. This is the direct downstream consequence of the proved finite-window Dirac law and proved step-from-Dirac theorem, and is the blocker for the original cadlag chain.
-- source:
--   Kyprianou Chapter 2, source-exact correction of d17f62e1-... and original LevyStochCalc Poisson/Atomic.lean.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteRegionPoissonLocallyFiniteStepRepresentationV2
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
