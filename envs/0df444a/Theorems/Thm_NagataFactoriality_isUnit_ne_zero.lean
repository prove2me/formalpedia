-- Prove2me | Theorems.Thm_NagataFactoriality_isUnit_ne_zero
-- name    : NagataFactoriality.isUnit_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:11.404029+00:00
-- url     : https://prove2.me/theorems/dc962dc7-c01e-5a26-877f-660e5657cea8
-- title:
--   Nagata Factoriality: is Unit ne zero
-- statement:
--   The Nagata Factoriality construction uses the is Unit ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L51-L52
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L51-L52

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators

theorem NagataFactoriality.isUnit_ne_zero {α : Type*} [CommRing α] [IsDomain α] {a : α} (ha : IsUnit a) : a ≠ 0 := by sorry
