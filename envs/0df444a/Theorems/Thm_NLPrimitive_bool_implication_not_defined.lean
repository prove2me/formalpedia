-- Prove2me | Theorems.Thm_NLPrimitive_bool_implication_not_defined
-- name    : NLPrimitive.bool_implication_not_defined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:46.429799+00:00
-- url     : https://prove2.me/theorems/747d0797-e1c3-460f-a64b-1fd91d3fc074
-- title:
--   NLPrimitive: bool implication not defined
-- statement:
--   The NLPrimitive construction uses the bool implication not defined property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L238-L241
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L238-L241

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.bool_implication_not_defined :
    boolOps.arr false false ≠
    boolOps.neg (boolOps.compat false (boolOps.neg false)) := by sorry
