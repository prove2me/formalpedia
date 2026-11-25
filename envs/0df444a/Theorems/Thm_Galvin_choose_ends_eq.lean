-- Prove2me | Theorems.Thm_Galvin_choose_ends_eq
-- name    : Galvin.choose_ends_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:50:37.031656+00:00
-- url     : https://prove2.me/theorems/f661e83c-f137-4705-adbf-03e8b1731f6a
-- title:
--   Galvin: choose ends eq
-- statement:
--   The Galvin construction uses the choose ends eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L157-L159
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/Orientation.lean#L157-L159

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

theorem Galvin.choose_ends_eq (c : G.Coloring (Fin 2)) (e : G.edgeSet)
    (h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e) : h.choose = e := by sorry
