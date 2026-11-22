-- Prove2me | Theorems.Thm_Nock_Noun_cons_children_unique
-- name    : Nock.Noun.cons_children_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:27:41.662896+00:00
-- url     : https://prove2.me/theorems/42405294-c18e-42a4-83e6-c63acdff9b29
-- title:
--   Noun: cons children unique
-- statement:
--   The structural core of `Lem:decomp`: the children of a `cons` are unique — `cons` is
--       injective, so the decomposition `n = cons(nL,nR)` is well-defined (main.tex:1208).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L55-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L55-L57

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
open Nock.Noun

theorem Nock.Noun.cons_children_unique {l r l' r' : Noun} (h : Noun.cell l r = Noun.cell l' r') :
    l = l' ∧ r = r' := by sorry
