-- Prove2me | Theorems.Thm_Konig_lineGraph_chromaticNumber_of_colorable_two
-- name    : Konig.lineGraph_chromaticNumber_of_colorable_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:42.553878+00:00
-- url     : https://prove2.me/theorems/96ceb2b0-a0d9-410d-9ea9-200ab5cd02c4
-- title:
--   Konig: line Graph chromatic Number of colorable two
-- statement:
--   **Kőnig's edge-colouring theorem**, chromatic-number form: `χ'(G) = Δ(G)` for a finite
--   bipartite graph.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L242-L246
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L242-L246

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

theorem Konig.lineGraph_chromaticNumber_of_colorable_two [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.Colorable 2) :
    G.lineGraph.chromaticNumber = G.maxDegree := by sorry
