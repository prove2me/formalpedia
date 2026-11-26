-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_le
-- name    : LeanPool.K5MinorFreeChoosability.restrict_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:53.706325+00:00
-- url     : https://prove2.me/theorems/aa9de91e-ffcc-525c-a8c7-63ee880f868c
-- title:
--   K5 Minor Free Choosability: restrict le
-- statement:
--   The K5 Minor Free Choosability construction uses the restrict le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L44-L45
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L44-L45

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}

theorem LeanPool.K5MinorFreeChoosability.restrict_le (G : SimpleGraph W) (s : Set W) : restrict G s ≤ G := by sorry
