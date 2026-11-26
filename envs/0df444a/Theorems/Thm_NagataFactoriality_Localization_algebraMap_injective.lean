-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_algebraMap_injective
-- name    : NagataFactoriality.Localization.algebraMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:06.302478+00:00
-- url     : https://prove2.me/theorems/792ad1de-141a-4ab3-9ecf-48a60ec51f4b
-- title:
--   Localization: algebra Map injective
-- statement:
--   The Localization construction uses the algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L59-L60
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L59-L60

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.Localization.algebraMap_injective : Function.Injective (algebraMap α (Localization S)) := by sorry
