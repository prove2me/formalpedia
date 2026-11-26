-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_ConnSet_insert_adj
-- name    : LeanPool.K5MinorFreeChoosability.ConnSet.insert_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:11.808848+00:00
-- url     : https://prove2.me/theorems/416e27d5-81b7-524a-89ce-00ec6eb222d7
-- title:
--   Conn Set: insert adj
-- statement:
--   Adding a vertex adjacent to a connected set keeps it connected.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L169-L179
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L169-L179

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}

theorem LeanPool.K5MinorFreeChoosability.ConnSet.insert_adj {G : SimpleGraph W} {s : Set W} (h : ConnSet G s) {a b : W}
    (hb : b ∈ s) (hab : G.Adj a b) : ConnSet G (insert a s) := by sorry
