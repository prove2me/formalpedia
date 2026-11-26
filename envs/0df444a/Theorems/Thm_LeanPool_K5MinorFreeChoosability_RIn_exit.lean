-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_exit
-- name    : LeanPool.K5MinorFreeChoosability.RIn.exit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:30.155038+00:00
-- url     : https://prove2.me/theorems/d898b874-fb0f-56e1-aa87-21187940f945
-- title:
--   RIn: exit
-- statement:
--   Walks starting inside the set `P` and ending outside of it must leave `P` along an edge.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L93-L108
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L93-L108

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

theorem LeanPool.K5MinorFreeChoosability.RIn.exit {P : Set W} (h : RIn G s a b) (haP : a ∈ P) (hbP : b ∉ P) :
    ∃ p q, RIn G (s ∩ P) a p ∧ p ∈ s ∧ p ∈ P ∧ q ∈ s ∧ q ∉ P ∧ G.Adj p q := by sorry
