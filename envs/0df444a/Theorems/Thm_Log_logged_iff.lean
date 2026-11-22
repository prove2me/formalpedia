-- Prove2me | Theorems.Thm_Log_logged_iff
-- name    : Log.logged_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:07:14.873587+00:00
-- url     : https://prove2.me/theorems/6fbaaa20-812f-48bd-943f-b2e7399353f7
-- title:
--   Log: logged iff
-- statement:
--   The Log construction uses the logged iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L38-L39
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L38-L39

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log

theorem Log.logged_iff {e : es.Event} : logged es e ↔ ∃ e', e ## e' := by sorry
