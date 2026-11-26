-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_eulerDefect_removeFromCycle
-- name    : LeanPool.K5MinorFreeChoosability.eulerDefect_removeFromCycle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:17:37.8409+00:00
-- url     : https://prove2.me/theorems/e9708413-d526-59bf-b074-76acf787ebef
-- title:
--   K5 Minor Free Choosability: euler Defect remove From Cycle
-- statement:
--   Removing a dart from its `σ`-cycle does not increase the defect.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L176-L180
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L176-L180

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

theorem LeanPool.K5MinorFreeChoosability.eulerDefect_removeFromCycle (σ α : Perm D) (z : D) :
    eulerDefect (removeFromCycle σ z) α ≤ eulerDefect σ α := by sorry
