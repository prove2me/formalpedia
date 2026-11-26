-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_ConnSet_mono
-- name    : LeanPool.K5MinorFreeChoosability.ConnSet.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:11:55.054905+00:00
-- url     : https://prove2.me/theorems/cb015b67-39e7-4a49-a6e8-fe39e81cdf0c
-- title:
--   Conn Set: mono
-- statement:
--   The Conn Set construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L159-L161
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L159-L161

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}

theorem LeanPool.K5MinorFreeChoosability.ConnSet.mono {G G' : SimpleGraph W} {s : Set W} (h : ConnSet G s) (hG : G ≤ G') :
    ConnSet G' s := by sorry
