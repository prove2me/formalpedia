-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_of_add
-- name    : NagataFactoriality.Localization.of_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:10.619453+00:00
-- url     : https://prove2.me/theorems/c3f609b0-a8d8-586d-9aab-db9c9ec17846
-- title:
--   Localization: of add
-- statement:
--   The Localization construction uses the of add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L28-L29
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L28-L29

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.of_add (a b : α) : of (S := S) (a + b) = of (S := S) a + of (S := S) b := by sorry
