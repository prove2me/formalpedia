-- Prove2me | Theorems.Thm_Nock_msize_singleton
-- name    : Nock.msize_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:40.958091+00:00
-- url     : https://prove2.me/theorems/5a6b1321-31bd-4f47-b4cc-39a100ef6a33
-- title:
--   Nock: msize singleton
-- statement:
--   The Nock construction uses the msize singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L126-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L126-L127

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

theorem Nock.msize_singleton (a : Noun) : msize ({a} : Multiset Noun) = a.size := by sorry
