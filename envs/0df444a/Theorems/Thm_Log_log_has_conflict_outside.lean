-- Prove2me | Theorems.Thm_Log_log_has_conflict_outside
-- name    : Log.log_has_conflict_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:07:15.137562+00:00
-- url     : https://prove2.me/theorems/75f361eb-eaeb-4f93-ab61-b63832a530af
-- title:
--   Log: log has conflict outside
-- statement:
--   The Log construction uses the log has conflict outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L45-L48
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L45-L48

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log

theorem Log.log_has_conflict_outside {c : Conf es} {e : es.Event} (he : e ∈ log es c) :
    ∃ e' ∉ c.1, e ## e' := by sorry
