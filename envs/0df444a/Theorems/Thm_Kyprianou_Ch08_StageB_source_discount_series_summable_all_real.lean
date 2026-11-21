-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_discount_series_summable_all_real
-- name    : Kyprianou.Ch08.StageB.source_discount_series_summable_all_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:34:07.53901+00:00
-- url     : https://prove2.me/theorems/d2a2da01-d8c4-4bf6-a6ce-73c8cd1d2601
-- title:
--   Global pointwise summability of zero-discount source q-scale powers
-- statement:
--   The real scale-convolution power series Σq^nFn(x) converges at every real x for each q≥0. For x≥0 this is the Proved source_scale_discount_series_summable. For x<0 the source scale W0 vanishes and every higher causal integral is over an empty interval, so every term is zero. Needed by the generic Proved causal_geometric_weighted_series_integrable theorem.
-- source:
--   Kyprianou (2006) Lemma 8.3 p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_discount_series_summable_all_real
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∀ x : ℝ, Summable (fun n : ℕ =>
      q ^ n * scaleConvolutionPower (W 0) n x) := by
  sorry
end Kyprianou.Ch08.StageB
