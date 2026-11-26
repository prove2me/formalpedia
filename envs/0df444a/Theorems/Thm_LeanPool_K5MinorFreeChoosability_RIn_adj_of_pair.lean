-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_adj_of_pair
-- name    : LeanPool.K5MinorFreeChoosability.RIn.adj_of_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:10:31.30537+00:00
-- url     : https://prove2.me/theorems/7f59cc47-1189-4244-ae65-51bdcc6303b3
-- title:
--   RIn: adj of pair
-- statement:
--   Two vertices `a, b` of `s` with a path of length at most one inside `{a, b}`.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L122-L130
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L122-L130

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}

theorem LeanPool.K5MinorFreeChoosability.RIn.adj_of_pair (h : RIn G {a, b} a b) (hab : a ≠ b) : G.Adj a b := by sorry
