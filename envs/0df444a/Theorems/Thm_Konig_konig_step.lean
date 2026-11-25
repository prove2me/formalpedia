-- Prove2me | Theorems.Thm_Konig_konig_step
-- name    : Konig.konig_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:15:46.455923+00:00
-- url     : https://prove2.me/theorems/bc350569-2341-44ed-9a04-70c19550b4ca
-- title:
--   Konig: konig step
-- statement:
--   **Kőnig's extension step.** In a bipartite graph with at least `Δ(G)` colours, any uncoloured
--   edge can be coloured after recolouring.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L130-L164
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L130-L164

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

theorem Konig.konig_step [Fintype V] [Fintype C] [DecidableRel G.Adj]
    (s : G.Coloring (Fin 2)) (c : PEC G C)
    (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hadj : G.Adj x y)
    (hnone : c.col x y = none) :
    ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by sorry
