-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_vanishes_origin
-- name    : Kyprianou.Ch08.StageB.source_scale_convolution_vanishes_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:54:08.204731+00:00
-- url     : https://prove2.me/theorems/447b649a-4ba9-4cd2-bb67-4a61d5a68171
-- title:
--   Vanishing source q-scale causal convolution at zero reserve
-- statement:
--   For an actual source scale family, q≥0, the causal convolution (W0∗Wq)(x) tends to zero as x↓0. Both scale functions are positive continuous on [0,∞) and hence uniformly bounded on compact intervals; bound the convolution on (0,x] by x W0(x)Wq(x), which tends to zero. This exact analytic boundary lemma combines with the source positive-reserve Volterra resolvent and right continuity to show Wq(0)=W0(0), closing the origin case of Kyprianou (8.24).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3 (8.24) and Lemma 8.6, pp.221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter

namespace Kyprianou.Ch08.StageB

/-- The true q-scale causal convolution vanishes as reserve decreases to zero. -/
theorem source_scale_convolution_vanishes_origin
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Filter.Tendsto
      (fun x : ℝ => ∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (0 : ℝ)) := by
  sorry

end Kyprianou.Ch08.StageB
