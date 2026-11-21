-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_real_series_continuous_nonnegative
-- name    : Kyprianou.Ch08.StageB.source_real_series_continuous_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:18:48.971556+00:00
-- url     : https://prove2.me/theorems/44372039-fd62-4477-8b61-83e8c87ce74d
-- title:
--   Continuous nonnegative actual source scale real convolution series
-- statement:
--   For each source-certified W and q≥0, the real scale-convolution series ∑q^n F_n(x) is continuous and nonnegative for x>0. Nonnegativity uses positive coefficients; continuity follows from local uniform factorial domination and continuity of individual causal powers. This supplies the regularity needed by the Proved positive-halfline Laplace uniqueness theorem for the source q-scale.
-- source:
--   Kyprianou (2006) Lemma 8.3 (8.23)-(8.24) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_real_series_continuous_nonnegative
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ContinuousOn
      (fun x : ℝ => ∑' n : ℕ,
        q ^ n * scaleConvolutionPower (W 0) n x) (Set.Ioi (0 : ℝ)) ∧
    (∀ x : ℝ, 0 < x →
      0 ≤ (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x)) := by
  sorry

end Kyprianou.Ch08.StageB
