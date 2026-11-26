-- Prove2me | Theorems.Thm_NagataFactoriality_IsNoetherianRing_hasFactorization
-- name    : NagataFactoriality.IsNoetherianRing.hasFactorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:16.453494+00:00
-- url     : https://prove2.me/theorems/35e3d5fb-16b9-5b93-a9fb-bf430fc19a29
-- title:
--   Is Noetherian Ring: has Factorization
-- statement:
--   The Is Noetherian Ring construction uses the has Factorization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Noetherian.lean#L10-L13
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Noetherian.lean#L10-L13

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Basic_Noetherian
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.IsNoetherianRing.hasFactorization {α : Type*} [CommRing α] [IsDomain α]
    (h : IsNoetherianRing α) : WfDvdMonoid α := by sorry
