-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_mk_eq_iff
-- name    : NagataFactoriality.Localization.mk_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:08.889804+00:00
-- url     : https://prove2.me/theorems/d926fcc3-e002-52a0-9a76-903d6383afd5
-- title:
--   Localization: mk eq iff
-- statement:
--   The Localization construction uses the mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L62-L81
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L62-L81

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.Localization.mk_eq_iff {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    mk (S := S) a s hs = mk (S := S) b t ht ↔ a * t = b * s := by sorry
