-- Prove2me | Theorems.Thm_NagataFactoriality_IsLocalization_dvd_map_iff
-- name    : NagataFactoriality.IsLocalization.dvd_map_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:18.856709+00:00
-- url     : https://prove2.me/theorems/b68674f0-699e-4061-8a48-2d7f3c1442a7
-- title:
--   Is Localization: dvd map iff
-- statement:
--   The Is Localization construction uses the dvd map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L62-L89
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L62-L89

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.IsLocalization.dvd_map_iff {a b : α} :
    algebraMap α β a ∣ algebraMap α β b ↔ ∃ s : α, s ∈ S ∧ a ∣ s * b := by sorry
