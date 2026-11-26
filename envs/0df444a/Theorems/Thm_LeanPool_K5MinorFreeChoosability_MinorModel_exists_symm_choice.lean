-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_MinorModel_exists_symm_choice
-- name    : LeanPool.K5MinorFreeChoosability.MinorModel.exists_symm_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:19:18.11449+00:00
-- url     : https://prove2.me/theorems/036f3e9c-c6b6-59e4-80e5-4fd73555116f
-- title:
--   Minor Model: exists symm choice
-- statement:
--   A symmetric choice of one dart of `G` for every dart of `H`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L71-L104
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorClosed.lean#L71-L104

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

theorem LeanPool.K5MinorFreeChoosability.MinorModel.exists_symm_choice :
    ∃ cd : H.Dart → G.Dart, (∀ e, (cd e).fst ∈ M.branch e.fst) ∧
      (∀ e, (cd e).snd ∈ M.branch e.snd) ∧ ∀ e, cd e.symm = (cd e).symm := by sorry
