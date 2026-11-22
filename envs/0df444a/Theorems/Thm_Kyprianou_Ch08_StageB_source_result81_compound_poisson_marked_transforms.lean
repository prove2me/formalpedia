-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_compound_poisson_marked_transforms
-- name    : Kyprianou.Ch08.StageB.source_result81_compound_poisson_marked_transforms
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:51:02.442886+00:00
-- url     : https://prove2.me/theorems/43c431f7-1957-425e-8c07-65589f39d757
-- title:
--   Poisson marked sum with nonpositive marks has both transforms
-- statement:
--   A positive-rate compound Poisson law with nonpositive marks has the characteristic transform and every nonnegative real Laplace transform. The same probability law is used for both transforms.
-- source:
--   Finite-activity construction in the Lévy-Khintchine cutoff argument for Kyprianou (2006), Ch. 8, Theorem 8.1. Parent Prove2Me theorem d6b08b21-0232-4da0-9092-8b64ae06523d.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_compound_poisson_marked_transforms
    (J : Measure ℝ) [IsProbabilityMeasure J] (hJ : ∀ᵐ y ∂J, y ≤ 0)
    (r : ℝ≥0) (hr : 0 < r) (t : ℝ≥0) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ ξ : ℝ, charFun (μ : Measure ℝ) ξ =
        Complex.exp ((((r : ℝ) * (t : ℝ) : ℝ) : ℂ) * (charFun J ξ - 1))) ∧
      (∀ β : ℝ, 0 ≤ β → Integrable (fun x => Real.exp (β * x)) (μ : Measure ℝ) ∧
        (∫ x, Real.exp (β * x) ∂(μ : Measure ℝ)) =
          Real.exp ((r : ℝ) * (t : ℝ) * ((∫ y, Real.exp (β * y) ∂J) - 1))) := by
  sorry
