-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_sameCycle_mulSwap
-- name    : LeanPool.K5MinorFreeChoosability.sameCycle_of_sameCycle_mulSwap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:05.927796+00:00
-- url     : https://prove2.me/theorems/5f33ae8b-24ca-4ebf-8c15-ef1d3b0209c6
-- title:
--   K5 Minor Free Choosability: same Cycle of same Cycle mul Swap
-- statement:
--   If `x` and `y` lie in the same cycle of `π`, every cycle of `π * swap x y` lies inside
--   a cycle of `π`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L263-L276
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Orbits.lean#L263-L276

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

theorem LeanPool.K5MinorFreeChoosability.sameCycle_of_sameCycle_mulSwap {π : Perm α} {x y : α} (hxy : SameCycle π x y)
    {a b : α} (h : SameCycle (π * swap x y) a b) : SameCycle π a b := by sorry
