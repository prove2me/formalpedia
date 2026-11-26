-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_mk_eq_zero_iff
-- name    : NagataFactoriality.Localization.mk_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:52:26.056843+00:00
-- url     : https://prove2.me/theorems/7df84c02-b6b3-5895-90c5-3517cde2aad8
-- title:
--   Localization: mk eq zero iff
-- statement:
--   The Localization construction uses the mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L86-L88
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L86-L88

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem NagataFactoriality.Localization.mk_eq_zero_iff {a s : α} (hs : s ∈ S) : mk (S := S) a s hs = 0 ↔ a = 0 := by sorry
