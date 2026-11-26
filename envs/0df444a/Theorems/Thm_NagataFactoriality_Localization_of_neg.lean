-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_of_neg
-- name    : NagataFactoriality.Localization.of_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:34.379875+00:00
-- url     : https://prove2.me/theorems/8aa79056-7685-4339-8a6a-ff08fc636878
-- title:
--   Localization: of neg
-- statement:
--   The Localization construction uses the of neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L34-L35
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L34-L35

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.of_neg (a : α) : of (S := S) (-a) = -of (S := S) a := by sorry
