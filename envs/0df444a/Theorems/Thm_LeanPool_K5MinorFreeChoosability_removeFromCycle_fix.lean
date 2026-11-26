-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_fix
-- name    : LeanPool.K5MinorFreeChoosability.removeFromCycle_fix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:19:28.835942+00:00
-- url     : https://prove2.me/theorems/7f00fb99-35af-55d6-a65c-72152c1b4657
-- title:
--   K5 Minor Free Choosability: remove From Cycle fix
-- statement:
--   The K5 Minor Free Choosability construction uses the remove From Cycle fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L144-L147
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L144-L147

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

theorem LeanPool.K5MinorFreeChoosability.removeFromCycle_fix {D : Type*} [DecidableEq D] {π : Perm D} {z u : D} (hu : π u = u)
    (huz : u ≠ z) : removeFromCycle π z u = u := by sorry
