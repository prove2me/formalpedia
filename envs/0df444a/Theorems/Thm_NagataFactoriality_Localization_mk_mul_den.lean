-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_mk_mul_den
-- name    : NagataFactoriality.Localization.mk_mul_den
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:22.400135+00:00
-- url     : https://prove2.me/theorems/c56209eb-bc1e-5b8a-a6d3-aa3779ffc8d3
-- title:
--   Localization: mk mul den
-- statement:
--   The Localization construction uses the mk mul den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L37-L40
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L37-L40

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.mk_mul_den (a s : α) (hs : s ∈ S) :
    mk (S := S) a s hs * of (S := S) s = of (S := S) a := by sorry
