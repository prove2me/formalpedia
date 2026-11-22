-- Prove2me | Theorems.Thm_Nock_runMset_cons
-- name    : Nock.runMset_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:39.664803+00:00
-- url     : https://prove2.me/theorems/6fe52d64-fc7b-47e7-bcef-75aa85ac5647
-- title:
--   Nock: run Mset cons
-- statement:
--   The Nock construction uses the run Mset cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L86-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L86-L89

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

theorem Nock.runMset_cons {m m' : Multiset Noun} {n : Noun} {ch : Option (Noun × Noun)}
    {ts : Transcript} (h : stepMset m n ch = some m') :
    runMset m ((n, ch) :: ts) = runMset m' ts := by sorry
