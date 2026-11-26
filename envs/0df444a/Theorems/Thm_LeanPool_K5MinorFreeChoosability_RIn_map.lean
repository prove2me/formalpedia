-- Prove2me | Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_map
-- name    : LeanPool.K5MinorFreeChoosability.RIn.map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:56.89118+00:00
-- url     : https://prove2.me/theorems/16792f82-6585-4516-80f0-cb474ea0467f
-- title:
--   RIn: map
-- statement:
--   Transport of reachability along a map sending each relevant edge to a reachable pair.
--
--   Source: https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L85-L90
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/LeanPool/K5MinorFreeChoosability/Reach.lean#L85-L90

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

theorem LeanPool.K5MinorFreeChoosability.RIn.map {W' : Type*} {G' : SimpleGraph W'} {t : Set W'} (f : W → W')
    (hf : ∀ x y, G.Adj x y → x ∈ s → y ∈ s → RIn G' t (f x) (f y))
    (h : RIn G s a b) : RIn G' t (f a) (f b) := by sorry
