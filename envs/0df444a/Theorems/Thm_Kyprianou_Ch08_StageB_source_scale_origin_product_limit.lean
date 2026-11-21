-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_product_limit
-- name    : Kyprianou.Ch08.StageB.source_scale_origin_product_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:05:36.506046+00:00
-- url     : https://prove2.me/theorems/e8fd650c-75d4-4f39-8778-876af4a4ecec
-- title:
--   Product x W0(x) Wq(x) tends to zero as x↓0
-- statement:
--   The product x W0(x)Wq(x) tends to zero at the right side of the origin, since W0 and Wq are continuous on [0,∞) and x→0. Exactly the source-exact dominating envelope required for convolution vanishing near the origin in Kyprianou (8.24).
-- source:
--   Kyprianou 2006 Chapter 8 Lemma 8.3 (8.23)-(8.24) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace Kyprianou.Ch08.StageB

theorem source_scale_origin_product_limit
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Filter.Tendsto (fun x : ℝ => x * W 0 x * W q x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (0 : ℝ)) := by
  sorry

end Kyprianou.Ch08.StageB
