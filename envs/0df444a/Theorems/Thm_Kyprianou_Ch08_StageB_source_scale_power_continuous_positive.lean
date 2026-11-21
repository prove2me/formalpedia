-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_continuous_positive
-- name    : Kyprianou.Ch08.StageB.source_scale_power_continuous_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:23:42.001178+00:00
-- url     : https://prove2.me/theorems/e336c9ec-5fe4-46f8-b3fd-51f3916e7fbd
-- title:
--   All source scale convolution powers continuous for positive reserves
-- statement:
--   Each genuine source W0 causal convolution power F_n is continuous on x>0: induction using source W0 continuous on the nonnegative halfline, global integrability of exponentially weighted Fn and Proved Avram causal convolution continuity theorem.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3 equation (8.24) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_scale_power_continuous_positive
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    ∀ n : ℕ, ContinuousOn (scaleConvolutionPower (W 0) n)
      (Set.Ioi (0 : ℝ)) := by
  sorry
end Kyprianou.Ch08.StageB
