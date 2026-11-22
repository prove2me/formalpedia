-- Prove2me | Theorems.Thm_Log_compatibleWithLog_conflict_in_log
-- name    : Log.compatibleWithLog_conflict_in_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:04:33.953882+00:00
-- url     : https://prove2.me/theorems/a33e412e-750c-4239-adb0-e38ab4fb5b26
-- title:
--   Log: compatible With Log conflict in log
-- statement:
--   The Log construction uses the compatible With Log conflict in log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L33-L35
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L33-L35

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R

theorem Log.compatibleWithLog_conflict_in_log {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) {e e' : F.Event} (he : e ∈ σ.1.1) (hconf : R e e') : e ∈ l := by sorry
