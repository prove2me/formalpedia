-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_mk_mul_mk
-- name    : NagataFactoriality.Localization.mk_mul_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:34.655553+00:00
-- url     : https://prove2.me/theorems/eb6c2089-5cea-555b-8883-f01d2a8dcdbd
-- title:
--   Localization: mk mul mk
-- statement:
--   The Localization construction uses the mk mul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L97-L101
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L97-L101

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.mk_mul_mk {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    mk (S := S) a s hs * mk (S := S) b t ht =
      mk (S := S) (a * b) (s * t) (S.mul_mem hs ht) := by sorry
