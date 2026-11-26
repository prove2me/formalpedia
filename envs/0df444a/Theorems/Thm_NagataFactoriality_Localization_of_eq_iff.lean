-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_of_eq_iff
-- name    : NagataFactoriality.Localization.of_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:19.864804+00:00
-- url     : https://prove2.me/theorems/6a59066e-f45e-527e-aed3-16ce2705fa67
-- title:
--   Localization: of eq iff
-- statement:
--   The Localization construction uses the of eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L83-L84
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L83-L84

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.Localization.of_eq_iff (a b : α) : of (S := S) a = of (S := S) b ↔ a = b := by sorry
