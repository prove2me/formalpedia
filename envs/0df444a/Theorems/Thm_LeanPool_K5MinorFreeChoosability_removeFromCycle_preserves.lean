-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_preserves
-- name    : LeanPool.K5MinorFreeChoosability.removeFromCycle_preserves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:20:02.237968+00:00
-- url     : https://prove2.me/theorems/13a0a469-1d81-414d-b7e7-b1457b367b9b
-- title:
--   K5 Minor Free Choosability: remove From Cycle preserves
-- statement:
--   The K5 Minor Free Choosability construction uses the remove From Cycle preserves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L135-L142
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L135-L142

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
variable [DecidableEq V]

theorem LeanPool.K5MinorFreeChoosability.removeFromCycle_preserves {D β : Type*} [DecidableEq D] (f : D → β) {π : Perm D}
    (hf : ∀ u, f (π u) = f u) (z : D) (u : D) : f (removeFromCycle π z u) = f u := by sorry
