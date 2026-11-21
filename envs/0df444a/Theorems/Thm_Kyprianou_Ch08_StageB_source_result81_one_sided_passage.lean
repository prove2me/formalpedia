-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_one_sided_passage
-- name    : Kyprianou.Ch08.StageB.source_result81_one_sided_passage
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:59:32.106189+00:00
-- url     : https://prove2.me/theorems/8f95e53d-1cfe-4e26-a9c2-0fa1c54631b2
-- title:
--   Theorem 8.1 one-sided discounted passage and ruin
-- statement:
--   Identify the law of the infimum at independent exponential killing, use the normalized Laplace transform and then pass to zero discount. Explain the positive finite slope case and the complementary case.
-- source:
--   Kyprianou (2006), Chapter 8, (8.6)–(8.7), pp. 214–215. Decomposition of dd90765c-572a-4a22-9657-966e9544f3d3.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_one_sided_passage
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    (∀ q x : ℝ, 0 < q →
      downExpectation P D.X q x = Zscale q (W q) x - q / Phi ψ q * W q x) ∧
    (∀ x d : ℝ, HasPositiveFiniteRightPsiSlope ψ d →
      downExpectation P D.X 0 x = 1 - d * W 0 x) ∧
    ((¬ ∃ d : ℝ, HasPositiveFiniteRightPsiSlope ψ d) →
      ∀ x : ℝ, downExpectation P D.X 0 x = 1) := by
  sorry
