-- Prove2me | Theorems.Thm_NagataFactoriality_dvd_mul_of_dvd_left
-- name    : NagataFactoriality.dvd_mul_of_dvd_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:56.893534+00:00
-- url     : https://prove2.me/theorems/cc5cd80a-1a50-5ecb-9464-536077834144
-- title:
--   Nagata Factoriality: dvd mul of dvd left
-- statement:
--   The Nagata Factoriality construction uses the dvd mul of dvd left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L30-L33
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L30-L33

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators

theorem NagataFactoriality.dvd_mul_of_dvd_left {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ b → a ∣ b * c := by sorry
