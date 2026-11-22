-- Prove2me | Theorems.Thm_NLDefined_canonical_countermodel
-- name    : NLDefined.canonical_countermodel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:26.105793+00:00
-- url     : https://prove2.me/theorems/1e9601b2-3218-4d6c-b497-567d5251efac
-- title:
--   NLDefined: canonical countermodel
-- statement:
--   The NLDefined construction uses the canonical countermodel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L181-L189
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L181-L189

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.canonical_countermodel {Γ : Formula → Prop} {a : Formula}
    (h : ¬ Derives Γ a) :
    (∀ b, Γ b → (canonical Γ).D (eval (canonical Γ).op Formula.var b)) ∧
    ¬ (canonical Γ).D (eval (canonical Γ).op Formula.var a) := by sorry
