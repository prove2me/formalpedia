-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_real_positive_x
-- name    : Kyprianou.Ch08.StageB.source_scale_discount_series_real_positive_x
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:16:02.655571+00:00
-- url     : https://prove2.me/theorems/9e35a616-c5be-456d-b13e-adef37267f7a
-- title:
--   Real q-scale convolution series at positive reserve
-- statement:
--   Actual source q-scale Wq(x) equals the real infinite convolution series of W0 for all q≥0 and x>0. This is the genuine source identity (8.24), to be proved using a geometric Laplace transform and uniqueness of nonnegative continuous functions.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3 p221

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_scale_discount_series_real_positive_x
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    W q x = ∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x := by
  sorry
end Kyprianou.Ch08.StageB
