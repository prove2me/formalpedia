-- Prove2me | Theorems.Thm_NLPrimitive_axiom_sound
-- name    : NLPrimitive.axiom_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:09.420492+00:00
-- url     : https://prove2.me/theorems/96934255-dde5-48c6-82d2-7f35c260fa66
-- title:
--   NLPrimitive: axiom sound
-- statement:
--   The NLPrimitive construction uses the axiom sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L125-L134
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L125-L134

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.axiom_sound {α : Type} (M : Matrix α) (v : Nat → α)
    {a : Formula} (h : Axiom a) : M.D (eval M.op v a) := by sorry
