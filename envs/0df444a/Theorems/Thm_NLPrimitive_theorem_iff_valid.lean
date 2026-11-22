-- Prove2me | Theorems.Thm_NLPrimitive_theorem_iff_valid
-- name    : NLPrimitive.theorem_iff_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:42.972814+00:00
-- url     : https://prove2.me/theorems/dd803c36-7918-4697-8093-cf02ae779d3b
-- title:
--   NLPrimitive: theorem iff valid
-- statement:
--   The NLPrimitive construction uses the theorem iff valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L196-L197
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L196-L197

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.theorem_iff_valid (a : Formula) : Theorem a ↔ Valid a := by sorry
