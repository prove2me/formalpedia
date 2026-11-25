-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_mem_uncoloured
-- name    : LeanPool.Vizing.PEC.mem_uncoloured
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:04:38.326752+00:00
-- url     : https://prove2.me/theorems/2c636ca2-faa6-4b2d-8655-dc20dfb0c309
-- title:
--   PEC: mem uncoloured
-- statement:
--   The PEC construction uses the mem uncoloured property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Main.lean#L42-L45
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Main.lean#L42-L45

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
omit [DecidableEq V] [Fintype C] [DecidableEq C]

theorem LeanPool.Vizing.PEC.mem_uncoloured [DecidableRel G.Adj] (c : PEC G C) (p : V × V) :
    p ∈ c.uncoloured ↔ G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none := by sorry
