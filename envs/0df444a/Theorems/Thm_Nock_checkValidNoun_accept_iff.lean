-- Prove2me | Theorems.Thm_Nock_checkValidNoun_accept_iff
-- name    : Nock.checkValidNoun_accept_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:37.802689+00:00
-- url     : https://prove2.me/theorems/99ca7489-4d2d-4512-8e39-d8dfed71b438
-- title:
--   Nock: check Valid Noun accept iff
-- statement:
--   The Nock construction uses the check Valid Noun accept iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L105-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L105-L113

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
set_option autoImplicit true
@[expose] public section
public section
open Nock

theorem Nock.checkValidNoun_accept_iff (n₀ : Noun) (T : Transcript) :
    checkValidNoun n₀ T = Result.accept ↔ runMset {n₀} T = some 0 := by sorry
