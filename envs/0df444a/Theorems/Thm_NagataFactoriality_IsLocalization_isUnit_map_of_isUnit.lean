-- Prove2me | Theorems.Thm_NagataFactoriality_IsLocalization_isUnit_map_of_isUnit
-- name    : NagataFactoriality.IsLocalization.isUnit_map_of_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:32.654484+00:00
-- url     : https://prove2.me/theorems/a2161084-469c-5c33-84f9-e0ab01d56c1a
-- title:
--   Is Localization: is Unit map of is Unit
-- statement:
--   The Is Localization construction uses the is Unit map of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L102-L103
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L102-L103

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem NagataFactoriality.IsLocalization.isUnit_map_of_isUnit {a : α} (ha : IsUnit a) : IsUnit (algebraMap α β a) := by sorry
