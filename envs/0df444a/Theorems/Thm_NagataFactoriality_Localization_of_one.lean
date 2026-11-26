-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_of_one
-- name    : NagataFactoriality.Localization.of_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:05.868257+00:00
-- url     : https://prove2.me/theorems/104ce38a-328e-519d-ba1f-be903c197a06
-- title:
--   Localization: of one
-- statement:
--   The Localization construction uses the of one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L25-L26
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L25-L26

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.of_one : of (S := S) (1 : α) = 1 := by sorry
