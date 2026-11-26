-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_r_eq_of_sameCycle
-- name    : LeanPool.K5MinorFreeChoosability.r_eq_of_sameCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:19:44.096113+00:00
-- url     : https://prove2.me/theorems/3d54930a-0c67-4baf-b99a-b6ebc71e6ef7
-- title:
--   K5 Minor Free Choosability: r eq of same Cycle
-- statement:
--   The K5 Minor Free Choosability construction uses the r eq of same Cycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L127-L131
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L127-L131

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable (M : MinorModel G H) (inK : G.Dart → Prop)
variable {M inK}

theorem LeanPool.K5MinorFreeChoosability.r_eq_of_sameCycle {σ : Perm G.Dart} {r : V → V} (hr : ∀ z, r (σ z).fst = r z.fst)
    {a b : G.Dart} (h : SameCycle σ a b) : r a.fst = r b.fst := by sorry
