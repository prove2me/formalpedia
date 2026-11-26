-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_isUnit_mk_of_mem
-- name    : NagataFactoriality.Localization.isUnit_mk_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:11.82892+00:00
-- url     : https://prove2.me/theorems/4e7df5e2-418d-5f92-940e-0dcc64378a29
-- title:
--   Localization: is Unit mk of mem
-- statement:
--   The Localization construction uses the is Unit mk of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L116-L121
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L116-L121

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.isUnit_mk_of_mem {a s : α} (ha : a ∈ S) (hs : s ∈ S) :
    IsUnit (mk (S := S) a s hs) := by sorry
