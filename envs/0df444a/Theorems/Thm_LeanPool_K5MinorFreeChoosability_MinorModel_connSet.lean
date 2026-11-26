-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_MinorModel_connSet
-- name    : LeanPool.K5MinorFreeChoosability.MinorModel.connSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:30.578632+00:00
-- url     : https://prove2.me/theorems/be3aaab8-9bf5-4375-9f87-2158928ed7e5
-- title:
--   Minor Model: conn Set
-- statement:
--   The Minor Model construction uses the conn Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean#L96-L97
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean#L96-L97

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {V W : Type*}
variable {G : SimpleGraph V} {k : ℕ}
open LeanPool.K5MinorFreeChoosability.MinorModel
variable {H : SimpleGraph W} (M : MinorModel G H)

theorem LeanPool.K5MinorFreeChoosability.MinorModel.connSet (w : W) : ConnSet G ↑(M.branch w) := by sorry
