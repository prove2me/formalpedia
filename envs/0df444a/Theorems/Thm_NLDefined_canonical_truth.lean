-- Prove2me | Theorems.Thm_NLDefined_canonical_truth
-- name    : NLDefined.canonical_truth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:06.913936+00:00
-- url     : https://prove2.me/theorems/ef6ae17b-3827-4cfa-93b4-6eea2796f2f3
-- title:
--   NLDefined: canonical truth
-- statement:
--   The NLDefined construction uses the canonical truth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L164-L167
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L164-L167

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.canonical_truth (Γ : Formula → Prop) (a : Formula) :
    (canonical Γ).D (eval (canonical Γ).op Formula.var a) ↔ Derives Γ a := by sorry
