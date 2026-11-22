-- Prove2me | Theorems.Thm_NLDefined_nontrivial
-- name    : NLDefined.nontrivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:28.064792+00:00
-- url     : https://prove2.me/theorems/5edae47c-8e70-48a4-ae4e-f2fa0d9172f9
-- title:
--   NLDefined: nontrivial
-- statement:
--   The NLDefined construction uses the nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L271-L276
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L271-L276

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.nontrivial : ¬ Theorem (Formula.var 0) := by sorry
