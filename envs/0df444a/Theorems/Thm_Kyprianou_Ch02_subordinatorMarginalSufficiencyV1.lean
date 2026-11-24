-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatorMarginalSufficiencyV1
-- name    : Kyprianou.Ch02.subordinatorMarginalSufficiencyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:27:41.231387+00:00
-- url     : https://prove2.me/theorems/1c081b79-ea0d-4353-84a2-2032f0aa0792
-- title:
--   Subordinator triplet forces nonnegative Lévy marginals
-- statement:
--   Sufficiency at the one-time law level. Rewrite the exponent without compensation using the finite first jump moment and nonnegative drift; approximate by positive-jump compound Poisson laws and pass to a weak limit on the closed nonnegative half-line.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, subordinator criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatorMarginalSufficiencyV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure) →
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω) := by
  sorry
