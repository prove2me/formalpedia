-- Prove2me | Theorems.Thm_NLDefined_aristotle1
-- name    : NLDefined.aristotle1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:30.902417+00:00
-- url     : https://prove2.me/theorems/c60c4af0-7f0d-41b2-95e8-7448dc1af2ad
-- title:
--   NLDefined: aristotle1
-- statement:
--   The NLDefined construction uses the aristotle1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L279-L286
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L279-L286

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.aristotle1 (a : Formula) :
    Theorem (Formula.neg (formulaOps.arr a (Formula.neg a))) := by sorry
