-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_of_mul_mk
-- name    : NagataFactoriality.Localization.of_mul_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:44.779997+00:00
-- url     : https://prove2.me/theorems/07aa6886-a281-4ee1-b594-e4cf326e19a5
-- title:
--   Localization: of mul mk
-- statement:
--   The Localization construction uses the of mul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L103-L106
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L103-L106

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.of_mul_mk (a b s : α) (hs : s ∈ S) :
    of (S := S) a * mk (S := S) b s hs = mk (S := S) (a * b) s hs := by sorry
