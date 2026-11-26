-- Prove2me | Theorems.Thm_Kyprianou_Ch04_frozenPathRightContinuousV1
-- name    : Kyprianou.Ch04.frozenPathRightContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:25.851478+00:00
-- url     : https://prove2.me/theorems/b5ace7a3-0607-5c3f-af39-8db6d7279e22
-- title:
--   Deterministic freezing preserves right continuity
-- statement:
--   Compose right continuity with the continuous monotone minimum map on right neighbourhoods.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integral approximation.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem frozenPathRightContinuousV1 (Y : NNReal → ℝ) (T : NNReal)
    (hR : ∀ u, ContinuousWithinAt Y (Ici u) u) :
    ∀ u, ContinuousWithinAt (fun v => Y (min v T)) (Ici u) u := by
  sorry
end Kyprianou.Ch04
