-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_nonnegative
-- name    : Kyprianou.Ch08.StageB.source_real_discount_series_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:19:45.745728+00:00
-- url     : https://prove2.me/theorems/32c9c348-0cde-4f79-97e9-bbe461d22d7b
-- title:
--   Nonnegative real source convolution discount series
-- statement:
--   At every real location x, the sum of nonnegative terms q^n F_n(x) is nonnegative for any q≥0, since all source scale convolution powers are nonnegative. Use the Proved all-real coefficient positivity theorem and Mathlib tsum_nonneg. This is the positivity premise in Laplace uniqueness for Kyprianou Lemma 8.3.
-- source:
--   Kyprianou (2006) Lemma 8.3 (8.23) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_real_discount_series_nonnegative
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∀ x : ℝ, 0 ≤
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) := by
  sorry

end Kyprianou.Ch08.StageB
