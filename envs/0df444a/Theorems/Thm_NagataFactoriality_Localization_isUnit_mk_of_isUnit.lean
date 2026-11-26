-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_isUnit_mk_of_isUnit
-- name    : NagataFactoriality.Localization.isUnit_mk_of_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:55.29011+00:00
-- url     : https://prove2.me/theorems/535273a5-9b2a-4d61-a85d-9292fc0a15a0
-- title:
--   Localization: is Unit mk of is Unit
-- statement:
--   The Localization construction uses the is Unit mk of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L129-L137
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L129-L137

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.isUnit_mk_of_isUnit {a s : α} (ha : IsUnit a) (hs : s ∈ S) :
    IsUnit (mk (S := S) a s hs) := by sorry
