-- Prove2me | Theorems.Thm_NLDefined_axiom_sound
-- name    : NLDefined.axiom_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:07.629313+00:00
-- url     : https://prove2.me/theorems/2c1d7453-b93c-4650-9d01-c7da787d626a
-- title:
--   NLDefined: axiom sound
-- statement:
--   The NLDefined construction uses the axiom sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L124-L133
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L124-L133

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.axiom_sound {α : Type} (M : Matrix α) (v : Nat → α)
    {a : Formula} (h : Axiom a) : M.D (eval M.op v a) := by sorry
