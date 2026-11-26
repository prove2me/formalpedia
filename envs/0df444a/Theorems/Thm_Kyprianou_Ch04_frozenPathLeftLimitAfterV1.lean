-- Prove2me | Theorems.Thm_Kyprianou_Ch04_frozenPathLeftLimitAfterV1
-- name    : Kyprianou.Ch04.frozenPathLeftLimitAfterV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:25.923803+00:00
-- url     : https://prove2.me/theorems/2c34fb43-c1f8-53a6-91e0-6c68449ec8c0
-- title:
--   Frozen path strict left limit after the horizon
-- statement:
--   The frozen path is eventually constant to the left of any time strictly after the horizon.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integral approximation.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem frozenPathLeftLimitAfterV1 (Y : NNReal → ℝ) (T u : NNReal) (hu : T < u) :
    Tendsto (fun v => Y (min v T)) (𝓝[<] u) (𝓝 (Y T)) := by
  sorry
end Kyprianou.Ch04
