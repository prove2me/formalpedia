-- Prove2me | Theorems.Thm_Kyprianou_Ch04_weightedFiniteStepsV1
-- name    : Kyprianou.Ch04.weightedFiniteStepsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:50:37.864465+00:00
-- url     : https://prove2.me/theorems/8c4af1d8-7a3e-4fd0-b591-ea7b15586a8e
-- title:
--   Finite-window arbitrary weighted Poisson integrals have common finite-step representations
-- statement:
--   Finite-window arbitrary weighted Poisson integrals have common finite-step representations
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem weightedFiniteStepsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (g : ℝ × ℝ → Ω → ℝ)
    (hDirac : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) {p} • Measure.dirac p) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ (s : Finset (ℝ × ℝ))
      (weight : ℝ × ℝ → ℝ), ∀ t : ℝ≥0, t ≤ (T : ℝ≥0) →
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), g z ω ∂(N.N ω)) =
        ∑ p ∈ s, if p.1 ≤ (t : ℝ) then weight p else 0  := by
  sorry
end Kyprianou.Ch04
