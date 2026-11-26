-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_MinorModel_internal_symm
-- name    : LeanPool.K5MinorFreeChoosability.MinorModel.internal_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:19:12.429399+00:00
-- url     : https://prove2.me/theorems/fe9e72d4-b5c9-548a-a15e-42a39a02f51a
-- title:
--   Minor Model: internal symm
-- statement:
--   The Minor Model construction uses the internal symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L67-L68
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L67-L68

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
open LeanPool.K5MinorFreeChoosability.MinorModel
variable (M : MinorModel G H)

theorem LeanPool.K5MinorFreeChoosability.MinorModel.internal_symm {z : G.Dart} : M.Internal z.symm ↔ M.Internal z := by sorry
