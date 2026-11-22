-- Prove2me | Theorems.Thm_Log_logged_symm
-- name    : Log.logged_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:07:13.605147+00:00
-- url     : https://prove2.me/theorems/b58775be-c2f0-4ed4-a8a7-9d62c3c49c10
-- title:
--   Log: logged symm
-- statement:
--   Minimal conflict is symmetric, so its partner is logged too.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L42-L43
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L42-L43

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log

theorem Log.logged_symm {e e' : es.Event} (h : e ## e') : logged es e' := by sorry
