-- Prove2me | Theorems.Thm_Galvin_rankB_injective
-- name    : Galvin.rankB_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:14:46.879797+00:00
-- url     : https://prove2.me/theorems/484ed1bd-c76d-4d05-8ad5-ef30a91318e6
-- title:
--   Galvin: rank B injective
-- statement:
--   The Galvin construction uses the rank B injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L188-L201
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L188-L201

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem Galvin.rankB_injective (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {idx : V → ℕ} (hidx : Function.Injective idx) (w : V) :
    Function.Injective (rankB c φ idx w) := by sorry
