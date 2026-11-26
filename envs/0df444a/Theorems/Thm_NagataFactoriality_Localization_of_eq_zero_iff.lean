-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_of_eq_zero_iff
-- name    : NagataFactoriality.Localization.of_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:35.193465+00:00
-- url     : https://prove2.me/theorems/85dadadf-2b90-4ab7-8900-b6c08c991960
-- title:
--   Localization: of eq zero iff
-- statement:
--   The Localization construction uses the of eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L90-L93
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L90-L93

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.Localization.of_eq_zero_iff (a : α) : of (S := S) a = 0 ↔ a = 0 := by sorry
