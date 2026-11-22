-- Prove2me | Theorems.Thm_NLPrimitive_canonical_countermodel
-- name    : NLPrimitive.canonical_countermodel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:39.855506+00:00
-- url     : https://prove2.me/theorems/cc03c209-641d-4e47-8685-0675eae2a69a
-- title:
--   NLPrimitive: canonical countermodel
-- statement:
--   The NLPrimitive construction uses the canonical countermodel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L182-L190
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L182-L190

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.canonical_countermodel {Γ : Formula → Prop} {a : Formula}
    (h : ¬ Derives Γ a) :
    (∀ b, Γ b → (canonical Γ).D (eval (canonical Γ).op Formula.var b)) ∧
    ¬ (canonical Γ).D (eval (canonical Γ).op Formula.var a) := by sorry
