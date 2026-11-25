-- Prove2me | Theorems.Thm_LeanPool_Vizing_PEC_vizing_step
-- name    : LeanPool.Vizing.PEC.vizing_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:03:34.364113+00:00
-- url     : https://prove2.me/theorems/d86dff31-9a2d-4cef-bd6b-72cfaac2c0b4
-- title:
--   PEC: vizing step
-- statement:
--   **Vizing's extension step.**
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Step.lean#L78-L208
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Step.lean#L78-L208

module
public import Definitions.Def_LeanPool_Vizing_Fan
public import Definitions.Def_LeanPool_Vizing_Step
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}
omit [DecidableEq V] [DecidableEq C]

theorem LeanPool.Vizing.PEC.vizing_step [DecidableRel G.Adj] (c : PEC G C) (hcard : G.maxDegree < Fintype.card C)
    {x y : V} (hadj : G.Adj x y) (hnone : c.col x y = none) :
    ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by sorry
