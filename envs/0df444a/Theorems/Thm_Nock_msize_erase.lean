-- Prove2me | Theorems.Thm_Nock_msize_erase
-- name    : Nock.msize_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:42.76169+00:00
-- url     : https://prove2.me/theorems/a942faf8-4552-42fe-9458-003ec26ad88e
-- title:
--   Nock: msize erase
-- statement:
--   The Nock construction uses the msize erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L129-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L129-L132

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

theorem Nock.msize_erase {n : Noun} {m : Multiset Noun} (h : n ∈ m) :
    msize m = n.size + msize (m.erase n) := by sorry
