-- Prove2me | Theorems.Thm_NLPrimitive_sound_complete
-- name    : NLPrimitive.sound_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:22.719692+00:00
-- url     : https://prove2.me/theorems/ffb43ae7-f7ff-4163-a836-7ab32fc51cbf
-- title:
--   NLPrimitive: sound complete
-- statement:
--   The NLPrimitive construction uses the sound complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L178-L180
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLPrimitive.lean#L178-L180

import Std
import Definitions.Def_NLPrimitive
set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive

theorem NLPrimitive.sound_complete (Γ : Formula → Prop) (a : Formula) :
    Derives Γ a ↔ Entails Γ a := by sorry
