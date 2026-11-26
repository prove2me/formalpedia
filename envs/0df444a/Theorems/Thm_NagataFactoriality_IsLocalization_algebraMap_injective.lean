-- Prove2me | Theorems.Thm_NagataFactoriality_IsLocalization_algebraMap_injective
-- name    : NagataFactoriality.IsLocalization.algebraMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:22.61349+00:00
-- url     : https://prove2.me/theorems/b394bed4-0625-492f-8932-9c2496d03fb0
-- title:
--   Is Localization: algebra Map injective
-- statement:
--   The Is Localization construction uses the algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L32-L35
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L32-L35

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.IsLocalization.algebraMap_injective (S : Submonoid α) [Fact ((0 : α) ∉ S)] [_root_.IsLocalization S β] :
    Function.Injective (algebraMap α β) := by sorry
