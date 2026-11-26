-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RedInv_finish
-- name    : LeanPool.K5MinorFreeChoosability.RedInv.finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:20:16.583547+00:00
-- url     : https://prove2.me/theorems/31372708-343c-4494-834c-13ef68665e52
-- title:
--   Red Inv: finish
-- statement:
--   The common final part of a deletion or contraction step.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L150-L206
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L150-L206

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

theorem LeanPool.K5MinorFreeChoosability.RedInv.finish {A : Finset G.Dart} {σ α σ₁ : Perm G.Dart} {r r' : V → V}
    (I : RedInv M inK A σ α r) {z : G.Dart} (hzA : z ∈ A) (hzK : ¬ inK z)
    (hKsymm : ∀ z, inK z → inK z.symm)
    (P1 : ∀ u, u ∉ A → σ₁ u = u) (P2 : ∀ u, r' (σ₁ u).fst = r' u.fst)
    (P3 : ∀ u ∈ A, ∀ v ∈ A, u ≠ z → u ≠ z.symm → v ≠ z → v ≠ z.symm →
      r' u.fst = r' v.fst → SameCycle σ₁ u v)
    (P4 : ∀ u v, r' u = r' v → M.SameBranch u v)
    (P5 : ∀ u, (u ∉ A ∨ u = z ∨ u = z.symm) → M.Internal u → r' u.fst = r' u.snd) :
    RedInv M inK ((A.erase z).erase z.symm)
      (removeFromCycle (removeFromCycle σ₁ z) z.symm) (α * swap z z.symm) r' := by sorry
