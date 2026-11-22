-- Prove2me | Theorems.Thm_NLPrimitive_canonical_truth
-- name    : NLPrimitive.canonical_truth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:06.633116+00:00
-- url     : https://prove2.me/theorems/9a071d1f-6932-402f-a7c6-f46cf3b6a91e
-- title:
--   NLPrimitive: canonical truth
-- statement:
--   The NLPrimitive construction uses the canonical truth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L165-L168
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L165-L168

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.canonical_truth (Γ : Formula → Prop) (a : Formula) :
    (canonical Γ).D (eval (canonical Γ).op Formula.var a) ↔ Derives Γ a := by sorry
