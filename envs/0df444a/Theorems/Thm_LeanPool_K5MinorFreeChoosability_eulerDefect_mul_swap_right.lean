-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_mul_swap_right
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_mul_swap_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:03.525189+00:00
-- url     : https://prove2.me/theorems/6230934c-4aee-5ef6-88d5-3ad9cf220977
-- title:
--   K5 Minor Free Choosability: euler Defect mul swap right
-- statement:
--   Splitting a cycle of `α` (for a map: detaching the two darts of an edge from each other)
--   does not increase the defect.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L140-L151
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L140-L151

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

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_mul_swap_right {σ α : Perm D} {x y : D} (hne : x ≠ y)
    (h : SameCycle α x y) : eulerDefect σ (α * swap x y) ≤ eulerDefect σ α := by sorry
