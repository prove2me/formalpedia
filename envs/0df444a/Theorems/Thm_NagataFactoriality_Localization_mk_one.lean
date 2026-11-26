-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_mk_one
-- name    : NagataFactoriality.Localization.mk_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:03.590711+00:00
-- url     : https://prove2.me/theorems/486a0645-b8bd-5afa-be43-96f31d37e8c3
-- title:
--   Localization: mk one
-- statement:
--   The Localization construction uses the mk one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L18-L20
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L18-L20

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.mk_one (a : α) : mk (S := S) a 1 S.one_mem = of (S := S) a := by sorry
