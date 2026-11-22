-- Prove2me | Theorems.Thm_NLPrimitive_nontrivial
-- name    : NLPrimitive.nontrivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:47.742838+00:00
-- url     : https://prove2.me/theorems/41d3b919-2c9a-4e9a-ad92-43385942283a
-- title:
--   NLPrimitive: nontrivial
-- statement:
--   The NLPrimitive construction uses the nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L230-L235
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L230-L235

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.nontrivial : ¬ Theorem (Formula.var 0) := by sorry
