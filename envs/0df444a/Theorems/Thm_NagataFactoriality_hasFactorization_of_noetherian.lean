-- Prove2me | Theorems.Thm_NagataFactoriality_hasFactorization_of_noetherian
-- name    : NagataFactoriality.hasFactorization_of_noetherian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:44.075792+00:00
-- url     : https://prove2.me/theorems/61a3665f-d65e-41f4-87f1-9aebbf79e6d7
-- title:
--   Nagata Factoriality: has Factorization of noetherian
-- statement:
--   The Nagata Factoriality construction uses the has Factorization of noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Noetherian.lean#L6-L8
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Noetherian.lean#L6-L8

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Basic_Noetherian
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.hasFactorization_of_noetherian {α : Type*} [CommRing α] [IsDomain α]
    [IsNoetherianRing α] : WfDvdMonoid α := by sorry
