-- Prove2me | Theorems.Thm_Log_label_mem_labelLog
-- name    : Log.label_mem_labelLog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:27.917117+00:00
-- url     : https://prove2.me/theorems/40ae743e-c8b5-4d45-aebf-6c32f2063bbc
-- title:
--   Log: label mem label Log
-- statement:
--   The Log construction uses the label mem label Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L52-L53
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L52-L53

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R

theorem Log.label_mem_labelLog {l : Set F.Event} {e : F.Event} (h : e ∈ l) :
    F.label e ∈ labelLog F l := by sorry
