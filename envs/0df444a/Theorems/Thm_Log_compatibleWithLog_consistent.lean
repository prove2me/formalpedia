-- Prove2me | Theorems.Thm_Log_compatibleWithLog_consistent
-- name    : Log.compatibleWithLog_consistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:04:27.548807+00:00
-- url     : https://prove2.me/theorems/71bfce36-2b0d-47b0-ade6-17c1bf5cb2b9
-- title:
--   Log: compatible With Log consistent
-- statement:
--   The Log construction uses the compatible With Log consistent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L29-L31
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L29-L31

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R

theorem Log.compatibleWithLog_consistent {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) {e e' : F.Event} (he : e ∈ σ.1.1) (he' : e' ∈ l) : ¬ R e e' := by sorry
