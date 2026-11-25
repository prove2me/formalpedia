-- Prove2me | Theorems.Thm_Konig_maxDegree_le_lineGraph_chromaticNumber
-- name    : Konig.maxDegree_le_lineGraph_chromaticNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:15:13.909083+00:00
-- url     : https://prove2.me/theorems/ac876734-bfdd-40e2-98b9-d125bbf50bea
-- title:
--   Konig: max Degree le line Graph chromatic Number
-- statement:
--   The edges at a vertex of maximum degree are pairwise adjacent in the line graph, so
--   `Δ(G) ≤ χ'(G)`.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L218-L238
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L218-L238

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

theorem Konig.maxDegree_le_lineGraph_chromaticNumber [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (G.maxDegree : ℕ∞) ≤ G.lineGraph.chromaticNumber := by sorry
