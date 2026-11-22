-- Prove2me | Theorems.Thm_NLPrimitive_sound
-- name    : NLPrimitive.sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:03.264133+00:00
-- url     : https://prove2.me/theorems/e3122841-ae0f-46e8-ae40-871496e96211
-- title:
--   NLPrimitive: sound
-- statement:
--   The NLPrimitive construction uses the sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L136-L143
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L136-L143

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.sound {Γ : Formula → Prop} {a : Formula}
    (h : Derives Γ a) : Entails Γ a := by sorry
