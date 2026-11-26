-- Prove2me | Theorems.Thm_NagataFactoriality_IsLocalization_isUnit_map_of_mem
-- name    : NagataFactoriality.IsLocalization.isUnit_map_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:31.019256+00:00
-- url     : https://prove2.me/theorems/0a8280b6-2a99-551a-b2a3-38f81098ff7f
-- title:
--   Is Localization: is Unit map of mem
-- statement:
--   The Is Localization construction uses the is Unit map of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L99-L100
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L99-L100

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem NagataFactoriality.IsLocalization.isUnit_map_of_mem {s : α} (hs : s ∈ S) : IsUnit (algebraMap α β s) := by sorry
