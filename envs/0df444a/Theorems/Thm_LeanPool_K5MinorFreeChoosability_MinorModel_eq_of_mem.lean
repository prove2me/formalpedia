-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_MinorModel_eq_of_mem
-- name    : LeanPool.K5MinorFreeChoosability.MinorModel.eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:22.562168+00:00
-- url     : https://prove2.me/theorems/ce24d086-44c0-5844-b9fd-281b774606e2
-- title:
--   Minor Model: eq of mem
-- statement:
--   The Minor Model construction uses the eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean#L91-L94
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/MinorModel.lean#L91-L94

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

theorem LeanPool.K5MinorFreeChoosability.MinorModel.eq_of_mem {w w' : W} {v : V} (hv : v ∈ M.branch w) (hv' : v ∈ M.branch w') :
    w = w' := by sorry
