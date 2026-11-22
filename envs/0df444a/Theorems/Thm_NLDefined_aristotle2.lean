-- Prove2me | Theorems.Thm_NLDefined_aristotle2
-- name    : NLDefined.aristotle2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:30.492093+00:00
-- url     : https://prove2.me/theorems/8a2a6a64-ae41-426c-b664-9f33ef1239ac
-- title:
--   NLDefined: aristotle2
-- statement:
--   The NLDefined construction uses the aristotle2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L288-L295
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L288-L295

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.aristotle2 (a : Formula) :
    Theorem (Formula.neg (formulaOps.arr (Formula.neg a) a)) := by sorry
