-- Prove2me | Theorems.Thm_Nock_step_msize
-- name    : Nock.step_msize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:46.516505+00:00
-- url     : https://prove2.me/theorems/75c64da7-c286-43f4-972d-bd0415f2f66e
-- title:
--   Nock: step msize
-- statement:
--   Each successful step of the walk removes exactly one node from the total (`Lem:pbt_size`
--       bookkeeping): a leaf pops `1` node; a cell pops `1 + |l| + |r|` and pushes `|l| + |r|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L136-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L136-L164

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

theorem Nock.step_msize {m m' : Multiset Noun} {n : Noun} {ch : Option (Noun × Noun)}
    (h : stepMset m n ch = some m') : msize m = msize m' + 1 := by sorry
