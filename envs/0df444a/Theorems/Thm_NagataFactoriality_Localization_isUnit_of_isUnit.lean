-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_isUnit_of_isUnit
-- name    : NagataFactoriality.Localization.isUnit_of_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:15.348863+00:00
-- url     : https://prove2.me/theorems/233c8b6b-a5d5-5409-9c79-a009ffe10427
-- title:
--   Localization: is Unit of is Unit
-- statement:
--   The Localization construction uses the is Unit of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L126-L127
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L126-L127

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.isUnit_of_isUnit {a : α} (ha : IsUnit a) : IsUnit (of (S := S) a) := by sorry
