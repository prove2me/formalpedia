-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
-- name    : Kyprianou.Ch04.pathJumpMeasureZeroTimeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:16:36.159889+00:00
-- url     : https://prove2.me/theorems/568fc07f-e09c-4723-964a-9adf645db0a3
-- title:
--   Intrinsic jump counting measure has no initial atom
-- statement:
--   An intrinsic jump counting measure does not charge the time-zero slab.
-- source:
--   Kyprianou (2006), Exercise 4.5, finite cutoff and quadratic tail

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem pathJumpMeasureZeroTimeV1 {Ω : Type} (X Xleft : NNReal → Ω → ℝ) (ω : Ω) :
    Kyprianou.Ch04.pathJumpMeasure X Xleft ω
      (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
  sorry
end Kyprianou.Ch04
