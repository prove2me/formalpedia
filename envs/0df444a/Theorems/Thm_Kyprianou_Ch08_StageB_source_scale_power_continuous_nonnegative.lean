-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_continuous_nonnegative
-- name    : Kyprianou.Ch08.StageB.source_scale_power_continuous_nonnegative
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:23:40.121818+00:00
-- url     : https://prove2.me/theorems/b8d87836-0569-4b73-9134-02ed617530b4
-- title:
--   Continuous source scale convolution coefficients through the origin
-- statement:
--   Each genuine source causal convolution power is continuous on [0,∞), including zero where convolution power F_(n+1)(0)=0. Combine positive x continuity from the Proved source_scale_power_continuous_positive with a zero-limit product integral estimate and source W0 right continuity. Needed for compact uniform series.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3 p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_scale_power_continuous_nonnegative
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    ∀ n : ℕ, ContinuousOn (scaleConvolutionPower (W 0) n)
      (Set.Ici (0 : ℝ)) := by
  sorry
end Kyprianou.Ch08.StageB
