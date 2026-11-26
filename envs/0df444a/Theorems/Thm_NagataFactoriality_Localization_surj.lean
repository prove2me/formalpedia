-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_surj
-- name    : NagataFactoriality.Localization.surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:06.705527+00:00
-- url     : https://prove2.me/theorems/8fb48cb3-b595-4009-83f5-3a3402550ea0
-- title:
--   Localization: surj
-- statement:
--   The Localization construction uses the surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L47-L50
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L47-L50

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.surj (z : Localization S) : ∃ a s, ∃ hs : s ∈ S, z = mk (S := S) a s hs := by sorry
