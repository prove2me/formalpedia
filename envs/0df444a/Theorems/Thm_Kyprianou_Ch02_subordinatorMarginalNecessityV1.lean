-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatorMarginalNecessityV1
-- name    : Kyprianou.Ch02.subordinatorMarginalNecessityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:27:37.081987+00:00
-- url     : https://prove2.me/theorems/34ced0ff-0a01-4b5d-b67f-ebbccebd6c8b
-- title:
--   Nonnegative Lévy marginals force subordinator triplet
-- statement:
--   Necessity of the subordinator triplet from almost sure nonnegative one-time marginals at every time. Use stationary increments and right continuity to obtain monotonicity, bounded variation for the Gaussian and first moment, then jump support and the finite-variation drift.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, subordinator criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatorMarginalNecessityV1
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
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω) →
    levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure := by
  sorry
