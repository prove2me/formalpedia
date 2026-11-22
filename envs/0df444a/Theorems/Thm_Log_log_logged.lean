-- Prove2me | Theorems.Thm_Log_log_logged
-- name    : Log.log_logged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:07:08.751796+00:00
-- url     : https://prove2.me/theorems/dd433ee9-2740-454d-8351-12ac6c941bbc
-- title:
--   Log: log logged
-- statement:
--   Events in the log are logged.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L30-L32
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L30-L32

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log

theorem Log.log_logged {c : Conf es} {e : es.Event} (h : e ∈ log es c) : logged es e := by sorry
