-- Prove2me | Theorems.Thm_NagataFactoriality_listProd_cons
-- name    : NagataFactoriality.listProd_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:19.985714+00:00
-- url     : https://prove2.me/theorems/68cf588d-2030-41bc-ae16-6ff7cdf6e0c5
-- title:
--   Nagata Factoriality: list Prod cons
-- statement:
--   The Nagata Factoriality construction uses the list Prod cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L14-L15
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L14-L15

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators

theorem NagataFactoriality.listProd_cons {α : Type*} [CommMonoid α] (a : α) (as : List α) :
    listProd (a :: as) = a * listProd as := by sorry

attribute [defeq] NagataFactoriality.listProd_cons
