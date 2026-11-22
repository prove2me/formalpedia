-- Prove2me | Theorems.Thm_NLDefined_sound_complete
-- name    : NLDefined.sound_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:11.277801+00:00
-- url     : https://prove2.me/theorems/cf8dbd57-2b87-4aa9-acc8-fe5b00d2b9f6
-- title:
--   NLDefined: sound complete
-- statement:
--   The NLDefined construction uses the sound complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L177-L179
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L177-L179

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.sound_complete (Γ : Formula → Prop) (a : Formula) :
    Derives Γ a ↔ Entails Γ a := by sorry
