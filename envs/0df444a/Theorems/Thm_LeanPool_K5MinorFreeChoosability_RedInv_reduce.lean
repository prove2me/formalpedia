-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RedInv_reduce
-- name    : LeanPool.K5MinorFreeChoosability.RedInv.reduce
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:19:50.021362+00:00
-- url     : https://prove2.me/theorems/f1b2a775-d1b0-5f69-8879-22d650badbd6
-- title:
--   Red Inv: reduce
-- statement:
--   Running the process until only kept darts remain.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L312-L333
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L312-L333

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable (M : MinorModel G H) (inK : G.Dart → Prop)
variable {M inK}
variable [DecidableEq V]
omit [DecidableEq V]

theorem LeanPool.K5MinorFreeChoosability.RedInv.reduce [Finite G.Dart] (hKsymm : ∀ z, inK z → inK z.symm) :
    ∀ (n : ℕ) (A : Finset G.Dart) (σ α : Perm G.Dart) (r : V → V), A.card = n →
      RedInv M inK A σ α r → ∃ A' σ' α' r', RedInv M inK A' σ' α' r' ∧
        (∀ z ∈ A', inK z) ∧ eulerDefect σ' α' ≤ eulerDefect σ α := by sorry
