-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedClockCoe
-- name    : Kyprianou.Ch04.clippedClockCoe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:24:34.422014+00:00
-- url     : https://prove2.me/theorems/69044b28-3220-48c9-9a89-ff7f9530a865
-- title:
--   clippedClockCoe
-- statement:
--   The finite clipping of the extended clock has the stated coercion.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open scoped NNReal
set_option autoImplicit false

/-- The finite deterministic clipping of an extended clock has the stated coercion. -/
theorem Kyprianou.Ch04.clippedClockCoe (tau : WithTop NNReal) (t : NNReal) :
    (((min tau (t : WithTop NNReal)).untopD t : NNReal) : WithTop NNReal) =
      min tau (t : WithTop NNReal)  := by
  sorry
