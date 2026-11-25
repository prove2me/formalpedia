-- Prove2me | Theorems.Thm_Konig_colour_walk
-- name    : Konig.colour_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:09:38.023903+00:00
-- url     : https://prove2.me/theorems/10c8a846-5a75-42e3-a732-a0934138f4ff
-- title:
--   Konig: colour walk
-- statement:
--   Along a walk of a graph contained in `G`, a proper 2-colouring of `G` changes at every step.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L62-L71
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L62-L71

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}

theorem Konig.colour_walk {H : SimpleGraph V} (hHG : H ≤ G) (s : G.Coloring (Fin 2)) {u v : V}
    (p : H.Walk u v) : (s v : ℕ) % 2 = ((s u : ℕ) + p.length) % 2 := by sorry
