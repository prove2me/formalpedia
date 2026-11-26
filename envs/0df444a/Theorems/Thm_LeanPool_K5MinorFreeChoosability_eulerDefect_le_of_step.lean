-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_le_of_step
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_le_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:45.437702+00:00
-- url     : https://prove2.me/theorems/6a87ad3c-2e12-5f3c-b52d-87f796c80bbd
-- title:
--   K5 Minor Free Choosability: euler Defect le of step
-- statement:
--   The abstract defect comparison used for all elementary operations.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L114-L136
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L114-L136

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable [DecidableEq D]
variable [Finite D]

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_le_of_step {σ α σ' α' : Perm D} {a b x y : D} (hab : a ≠ b)
    (hc : cycleCount σ' + cycleCount α' = cycleCount σ + cycleCount α + 1)
    (hφ : σ' * α' = σ * α * swap a b)
    (hK1 : ∀ u v, compSetoid σ α u v → addPairSetoid (compSetoid σ' α') x y u v)
    (hK2 : compSetoid σ' α' a b → ∀ u v, compSetoid σ α u v → compSetoid σ' α' u v) :
    eulerDefect σ' α' ≤ eulerDefect σ α := by sorry
