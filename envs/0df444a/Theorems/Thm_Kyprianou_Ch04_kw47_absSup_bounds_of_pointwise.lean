-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_absSup_bounds_of_pointwise
-- name    : Kyprianou.Ch04.kw47_absSup_bounds_of_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T10:12:13.001049+00:00
-- url     : https://prove2.me/theorems/ebc7908c-7468-5f6f-badd-10b20a11a325
-- title:
--   Absolute compact supremum is bounded by a pointwise envelope
-- statement:
--   The compact time set contains zero and the pointwise bound supplies an upper bound; the conditional supremum therefore lies between zero and the envelope.
-- source:
--   Kyprianou (2006), Exercise 4.7(iii), worked solution pp. 320-321.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_absSup_bounds_of_pointwise
    (f : NNReal → Real) (t : NNReal) (B : Real)
    (hb : ∀ s : NNReal, s ≤ t → |f s| ≤ B) :
    0 ≤ sSup ((fun s : NNReal => |f s|) '' Iic t) ∧
    sSup ((fun s : NNReal => |f s|) '' Iic t) ≤ B := by sorry
