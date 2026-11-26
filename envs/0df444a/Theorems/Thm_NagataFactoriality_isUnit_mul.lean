-- Prove2me | Theorems.Thm_NagataFactoriality_isUnit_mul
-- name    : NagataFactoriality.isUnit_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:21.662482+00:00
-- url     : https://prove2.me/theorems/4aff9abc-1b34-4e3c-91d3-77373ce6d7ec
-- title:
--   Nagata Factoriality: is Unit mul
-- statement:
--   The Nagata Factoriality construction uses the is Unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L42-L45
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L42-L45

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators

theorem NagataFactoriality.isUnit_mul {α : Type*} [CommMonoid α] {a b : α} :
    IsUnit a → IsUnit b → IsUnit (a * b) := by sorry
