-- Prove2me | Theorems.Thm_Log_log_mem_iff
-- name    : Log.log_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:07:15.805788+00:00
-- url     : https://prove2.me/theorems/fcd2ef73-7325-4530-b153-9cc7c1a063bc
-- title:
--   Log: log mem iff
-- statement:
--   The Log construction uses the log mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L34-L36
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L34-L36

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log

theorem Log.log_mem_iff {c : Conf es} {e : es.Event} :
    e ∈ log es c ↔ e ∈ c.1 ∧ ∃ e' ∉ c.1, e ## e' := by sorry
