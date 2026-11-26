-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RedInv_step
-- name    : LeanPool.K5MinorFreeChoosability.RedInv.step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:19:47.529255+00:00
-- url     : https://prove2.me/theorems/c93d2730-1973-5c9f-8354-9e6fdc7d369f
-- title:
--   Red Inv: step
-- statement:
--   One step of the process: delete or contract the edge of a dart outside the kept set.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L209-L308
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L209-L308

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

theorem LeanPool.K5MinorFreeChoosability.RedInv.step [Finite G.Dart] {A : Finset G.Dart} {σ α : Perm G.Dart}
    {r : V → V} (I : RedInv M inK A σ α r) {z : G.Dart} (hzA : z ∈ A) (hzK : ¬ inK z)
    (hKsymm : ∀ z, inK z → inK z.symm) :
    ∃ σ' α' r', RedInv M inK ((A.erase z).erase z.symm) σ' α' r' ∧
      eulerDefect σ' α' ≤ eulerDefect σ α := by sorry
