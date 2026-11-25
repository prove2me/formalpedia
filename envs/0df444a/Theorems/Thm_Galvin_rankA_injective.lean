-- Prove2me | Theorems.Thm_Galvin_rankA_injective
-- name    : Galvin.rankA_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:14:47.703565+00:00
-- url     : https://prove2.me/theorems/ba3bcc3c-7c8f-4d0e-b249-985ddda74ad2
-- title:
--   Galvin: rank A injective
-- statement:
--   The Galvin construction uses the rank A injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L175-L186
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L175-L186

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

theorem Galvin.rankA_injective (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {idx : V → ℕ} (hidx : Function.Injective idx) (m : V) :
    Function.Injective (rankA c φ idx m) := by sorry
