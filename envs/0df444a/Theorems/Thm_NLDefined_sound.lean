-- Prove2me | Theorems.Thm_NLDefined_sound
-- name    : NLDefined.sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:06.539373+00:00
-- url     : https://prove2.me/theorems/ccd53c57-2f3d-49c9-a7ed-a2c0f020a44b
-- title:
--   NLDefined: sound
-- statement:
--   The NLDefined construction uses the sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L135-L142
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L135-L142

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.sound {Γ : Formula → Prop} {a : Formula}
    (h : Derives Γ a) : Entails Γ a := by sorry
