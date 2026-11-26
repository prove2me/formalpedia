-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_rel_apply_of_mulSwap
-- name    : LeanPool.K5MinorFreeChoosability.rel_apply_of_mulSwap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:15:33.643199+00:00
-- url     : https://prove2.me/theorems/2281538d-9117-5a9e-a720-b755f1779edd
-- title:
--   K5 Minor Free Choosability: rel apply of mul Swap
-- statement:
--   A step of `π` is a step of `π * swap x y` once `x` and `y` are related.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L104-L109
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Planar/Hypermap.lean#L104-L109

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

theorem LeanPool.K5MinorFreeChoosability.rel_apply_of_mulSwap (s : Setoid D) (π : Perm D) (x y : D)
    (h : ∀ z, s z ((π * swap x y) z)) (hxy : s x y) (z : D) : s z (π z) := by sorry
