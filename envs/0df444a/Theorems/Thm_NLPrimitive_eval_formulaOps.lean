-- Prove2me | Theorems.Thm_NLPrimitive_eval_formulaOps
-- name    : NLPrimitive.eval_formulaOps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:11.408854+00:00
-- url     : https://prove2.me/theorems/76f11329-de94-4379-be0e-c4ae1ba0d052
-- title:
--   NLPrimitive: eval formula Ops
-- statement:
--   The NLPrimitive construction uses the eval formula Ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L161-L163
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L161-L163

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.eval_formulaOps (a : Formula) :
    eval formulaOps Formula.var a = a := by sorry
