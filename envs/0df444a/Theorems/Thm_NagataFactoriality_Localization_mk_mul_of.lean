-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_mk_mul_of
-- name    : NagataFactoriality.Localization.mk_mul_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:42.637793+00:00
-- url     : https://prove2.me/theorems/8982f5c2-dbf5-50f0-b5cf-eb9e763f1910
-- title:
--   Localization: mk mul of
-- statement:
--   The Localization construction uses the mk mul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L108-L114
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L108-L114

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.mk_mul_of (a b s : α) (hs : s ∈ S) :
    mk (S := S) a s hs * of (S := S) b = mk (S := S) (a * b) s hs := by sorry
