-- Prove2me | Theorems.Thm_NagataFactoriality_IsLocalization_map_eq_iff
-- name    : NagataFactoriality.IsLocalization.map_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:32.502419+00:00
-- url     : https://prove2.me/theorems/3955866b-7067-5f6b-969a-6a08e75fb7ed
-- title:
--   Is Localization: map eq iff
-- statement:
--   The Is Localization construction uses the map eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L48-L50
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L48-L50

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.IsLocalization.map_eq_iff (S : Submonoid α) [Fact ((0 : α) ∉ S)] [_root_.IsLocalization S β] (a b : α) :
    algebraMap α β a = algebraMap α β b ↔ a = b := by sorry
