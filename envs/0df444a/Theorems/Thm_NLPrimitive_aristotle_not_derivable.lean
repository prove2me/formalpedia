-- Prove2me | Theorems.Thm_NLPrimitive_aristotle_not_derivable
-- name    : NLPrimitive.aristotle_not_derivable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:46.632447+00:00
-- url     : https://prove2.me/theorems/743cf052-0200-4f47-bb45-535e46501708
-- title:
--   NLPrimitive: aristotle not derivable
-- statement:
--   The NLPrimitive construction uses the aristotle not derivable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L223-L228
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L223-L228

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.aristotle_not_derivable : ¬ Theorem aristotle := by sorry
