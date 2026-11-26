-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_connSet_reach
-- name    : LeanPool.K5MinorFreeChoosability.connSet_reach
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:22.24823+00:00
-- url     : https://prove2.me/theorems/aaf70f2f-f9cd-4dbf-b4ad-8e1c9c2852bd
-- title:
--   K5 Minor Free Choosability: conn Set reach
-- statement:
--   The vertices reachable from `a` inside `s` form a connected set.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L182-L190
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L182-L190

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}

theorem LeanPool.K5MinorFreeChoosability.connSet_reach (G : SimpleGraph W) (s : Set W) {a : W} (ha : a ∈ s) :
    ConnSet G {x | x ∈ s ∧ RIn G s a x} := by sorry
