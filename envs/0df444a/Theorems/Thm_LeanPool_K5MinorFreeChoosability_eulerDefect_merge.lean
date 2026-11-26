-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_merge
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_merge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:48.016666+00:00
-- url     : https://prove2.me/theorems/b637b980-aed8-4a17-8737-39709055ccaa
-- title:
--   K5 Minor Free Choosability: euler Defect merge
-- statement:
--   Contraction step: if the two darts `x`, `y = α x` of an edge lie in different
--   `σ`-cycles, merging those cycles while detaching `x` from `y` does not increase the defect;
--   the face permutation is unchanged.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L185-L209
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L185-L209

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

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_merge {σ α : Perm D} {x y : D} (hne : x ≠ y) (hαx : α x = y)
    (hαy : α y = x) (h : ¬ SameCycle σ x y) :
    eulerDefect (σ * swap x y) (α * swap x y) ≤ eulerDefect σ α := by sorry
