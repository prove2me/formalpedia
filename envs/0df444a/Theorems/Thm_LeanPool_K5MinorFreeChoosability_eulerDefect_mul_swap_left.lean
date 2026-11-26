-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_mul_swap_left
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_mul_swap_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:54.228568+00:00
-- url     : https://prove2.me/theorems/de2ead73-779c-5024-b9ef-4e32cf220e66
-- title:
--   K5 Minor Free Choosability: euler Defect mul swap left
-- statement:
--   Splitting a cycle of `σ` does not increase the defect.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L154-L173
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L154-L173

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

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_mul_swap_left {σ α : Perm D} {x y : D} (hne : x ≠ y)
    (h : SameCycle σ x y) : eulerDefect (σ * swap x y) α ≤ eulerDefect σ α := by sorry
