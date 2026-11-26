-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_dvd_of_iff
-- name    : NagataFactoriality.Localization.dvd_of_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:55.784985+00:00
-- url     : https://prove2.me/theorems/1af60dca-44b8-4e4e-8228-3d87b1dc6098
-- title:
--   Localization: dvd of iff
-- statement:
--   The Localization construction uses the dvd of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L143-L172
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L143-L172

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.Localization.dvd_of_iff {a b : α} :
    of (S := S) a ∣ of (S := S) b ↔ ∃ s : α, s ∈ S ∧ a ∣ s * b := by sorry
