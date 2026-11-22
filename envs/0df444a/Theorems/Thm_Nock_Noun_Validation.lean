-- Prove2me | Theorems.Thm_Nock_Noun_Validation
-- name    : Nock.Noun_Validation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:53.321567+00:00
-- url     : https://prove2.me/theorems/e010e9cb-fe49-48e6-abc4-40767d40ffb6
-- title:
--   Nock: Noun Validation
-- statement:
--   **`Thm:Noun_Validation`** (`main.tex:1268–1269`).
--       n ∈ N^λ(F) ⇔ ∃ T. CheckValidNoun(n;T)=Accept ∧ |T|=2λ−1
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L239-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L239-L255

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

theorem Nock.Noun_Validation (n : Noun) (lam : ℕ) :
    n.leaves = lam ↔
      ∃ T : Transcript, checkValidNoun n T = Result.accept ∧ T.length = 2 * lam - 1 := by sorry
