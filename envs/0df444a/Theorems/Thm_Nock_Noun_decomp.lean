-- Prove2me | Theorems.Thm_Nock_Noun_decomp
-- name    : Nock.Noun.decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:39.665897+00:00
-- url     : https://prove2.me/theorems/6717c7dd-e1d8-4dd5-9e11-529f53694d1c
-- title:
--   Noun: decomp
-- statement:
--   **`Lem:decomp`** (`main.tex:1210–1213`).
--       ∃! λ_L, λ_R ∈ ℕ₊ s.t. λ = λ_L + λ_R, n_L ∈ N^{λ_L}(F), n_R ∈ N^{λ_R}(F)
--       ⇔ n = cons(n_L,n_R), n ∈ N^λ(F).
--       (Lean ∃ also includes `n = cons(n_L,n_R)` per CORRESPONDENCE note 3.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L36-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L36-L51

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

theorem Nock.Noun.decomp (n nL nR : Noun) (lam : ℕ) :
    (∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ lam = p.1 + p.2 ∧
        nL.leaves = p.1 ∧ nR.leaves = p.2 ∧ n = Noun.cell nL nR)
      ↔ (n = Noun.cell nL nR ∧ n.leaves = lam) := by sorry
