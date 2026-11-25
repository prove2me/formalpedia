-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_exists_total
-- name    : LeanPool.Vizing.PEC.exists_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:04:54.421816+00:00
-- url     : https://prove2.me/theorems/b2dee168-3887-4c73-9a5e-da8575f65cf1
-- title:
--   PEC: exists total
-- statement:
--   Every graph has a proper edge colouring with more than `Δ` colours.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Main.lean#L49-L84
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Main.lean#L49-L84

module
public import Definitions.Def_LeanPool_Vizing_Step
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_LeanPool_Vizing_Main
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}
omit [DecidableEq V] [DecidableEq C]

theorem LeanPool.Vizing.PEC.exists_total [DecidableRel G.Adj] (hcard : G.maxDegree < Fintype.card C) :
    ∃ c : PEC G C, ∀ u v, G.Adj u v → c.col u v ≠ none := by sorry
