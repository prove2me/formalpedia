-- Prove2me | Theorems.Thm_Nock_msize_zero
-- name    : Nock.msize_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:35.976923+00:00
-- url     : https://prove2.me/theorems/4a564d24-53a7-46a6-b35f-5c878d306e3b
-- title:
--   Nock: msize zero
-- statement:
--   The Nock construction uses the msize zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L120-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L120-L120

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

theorem Nock.msize_zero : msize (0 : Multiset Noun) = 0 := by sorry
