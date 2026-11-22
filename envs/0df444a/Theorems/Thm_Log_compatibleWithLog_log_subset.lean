-- Prove2me | Theorems.Thm_Log_compatibleWithLog_log_subset
-- name    : Log.compatibleWithLog_log_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:04:29.236478+00:00
-- url     : https://prove2.me/theorems/3ec1fdbc-9a02-4bbe-b576-207b24ae66d3
-- title:
--   Log: compatible With Log log subset
-- statement:
--   The Log construction uses the compatible With Log log subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L26-L27
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Log.lean#L26-L27

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R

theorem Log.compatibleWithLog_log_subset {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) : l ⊆ σ.1.1 := by sorry
