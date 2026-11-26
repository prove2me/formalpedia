-- Prove2me | Theorems.Thm_NagataFactoriality_Localization_den_mul_mk
-- name    : NagataFactoriality.Localization.den_mul_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:51:38.545049+00:00
-- url     : https://prove2.me/theorems/93db6ec9-999a-4765-bd54-795ee779f679
-- title:
--   Localization: den mul mk
-- statement:
--   The Localization construction uses the den mul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L42-L45
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/Localization.lean#L42-L45

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}

theorem NagataFactoriality.Localization.den_mul_mk (a s : α) (hs : s ∈ S) :
    of (S := S) s * mk (S := S) a s hs = of (S := S) a := by sorry
