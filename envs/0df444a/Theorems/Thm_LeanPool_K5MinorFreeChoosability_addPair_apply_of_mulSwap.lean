-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_addPair_apply_of_mulSwap
-- name    : LeanPool.K5MinorFreeChoosability.addPair_apply_of_mulSwap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:25.70006+00:00
-- url     : https://prove2.me/theorems/6745e5dd-e33b-4653-a280-223037e4bd1a
-- title:
--   K5 Minor Free Choosability: add Pair apply of mul Swap
-- statement:
--   A step of `π` is a step of `π * swap x y` up to the pair `(x, y)`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L90-L101
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L90-L101

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

theorem LeanPool.K5MinorFreeChoosability.addPair_apply_of_mulSwap (s : Setoid D) (π : Perm D) (x y : D)
    (h : ∀ z, s z ((π * swap x y) z)) (z : D) : addPairSetoid s x y z (π z) := by sorry
