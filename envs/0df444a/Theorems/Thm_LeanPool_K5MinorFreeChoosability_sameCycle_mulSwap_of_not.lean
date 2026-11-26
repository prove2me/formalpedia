-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_mulSwap_of_not
-- name    : LeanPool.K5MinorFreeChoosability.sameCycle_mulSwap_of_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:01.612448+00:00
-- url     : https://prove2.me/theorems/9e547801-dfa4-50e2-af4e-99e46559641d
-- title:
--   K5 Minor Free Choosability: same Cycle mul Swap of not
-- statement:
--   If `x` and `y` lie in different cycles of `π`, they lie in the same cycle of
--   `π * swap x y`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L312-L319
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L312-L319

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]

theorem LeanPool.K5MinorFreeChoosability.sameCycle_mulSwap_of_not [Finite α] {π : Perm α} {x y : α}
    (h : ¬ SameCycle π x y) : SameCycle (π * swap x y) x y := by sorry
