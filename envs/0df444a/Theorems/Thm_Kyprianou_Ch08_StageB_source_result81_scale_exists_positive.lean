-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_exists_positive
-- name    : Kyprianou.Ch08.StageB.source_result81_scale_exists_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:59:33.397283+00:00
-- url     : https://prove2.me/theorems/4a5bedc9-ffce-4d0e-abf0-74c2a8cddb49
-- title:
--   Theorem 8.1 scale normalization and positivity
-- statement:
--   Construct nonnegative continuous scale functions with the normalized Laplace transform at all nonnegative discounts, and establish positivity at every strictly positive level. Use the descending ladder renewal or tilted survival construction and use the same law-derived exponent as the parent.
-- source:
--   Kyprianou (2006), Chapter 8, (8.5), pp. 214–215. Decomposition of dd90765c-572a-4a22-9657-966e9544f3d3.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_scale_exists_positive
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∃ W : ℝ → ℝ → ℝ, HasSourceScaleFamily ψ W ∧
      ∀ q a : ℝ, 0 ≤ q → 0 < a → 0 < W q a := by
  sorry
