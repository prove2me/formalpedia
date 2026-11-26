-- Prove2me | Theorems.Thm_NagataFactoriality_IsLocalization_surj
-- name    : NagataFactoriality.IsLocalization.surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:19.389561+00:00
-- url     : https://prove2.me/theorems/011a7bf7-5d4d-4685-b5de-a7564c128296
-- title:
--   Is Localization: surj
-- statement:
--   The Is Localization construction uses the surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L24-L26
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L24-L26

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem NagataFactoriality.IsLocalization.surj (z : β) : ∃ a s, ∃ hs : s ∈ S, z = _root_.IsLocalization.mk' β a ⟨s, hs⟩ := by sorry
