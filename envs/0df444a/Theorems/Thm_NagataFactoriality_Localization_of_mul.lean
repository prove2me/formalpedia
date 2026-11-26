-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_of_mul
-- name    : NagataFactoriality.Localization.of_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:27.085676+00:00
-- url     : https://prove2.me/theorems/04686baf-f406-4e7d-a8e1-e3cfc2d0d53f
-- title:
--   Localization: of mul
-- statement:
--   The Localization construction uses the of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L31-L32
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L31-L32

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.of_mul (a b : α) : of (S := S) (a * b) = of (S := S) a * of (S := S) b := by sorry
