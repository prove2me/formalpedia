-- Prove2me | Theorems.Thm_Log_log_subset
-- name    : Log.log_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:07:00.237428+00:00
-- url     : https://prove2.me/theorems/1f555eee-4238-4077-9b42-671a7acd609b
-- title:
--   Log: log subset
-- statement:
--   The log is contained in the configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L27-L27
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L27-L27

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log

theorem Log.log_subset {c : Conf es} : log es c ⊆ c.1 := by sorry
