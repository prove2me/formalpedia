-- Prove2me | Theorems.Thm_LeanPool_Vizing_degree_toSimpleGraph_le
-- name    : LeanPool.Vizing.degree_toSimpleGraph_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:59:23.399344+00:00
-- url     : https://prove2.me/theorems/85aa8ce8-c4f4-40b4-b745-a8796ab46e12
-- title:
--   Vizing: degree to Simple Graph le
-- statement:
--   Degrees can only drop when passing to the induced graph on a connected component.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Endpoints.lean#L29-L40
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Endpoints.lean#L29-L40

module
public import Definitions.Def_LeanPool_Vizing_Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Definitions.Def_LeanPool_Vizing_Endpoints
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V]

theorem LeanPool.Vizing.degree_toSimpleGraph_le {H : SimpleGraph V} [DecidableRel H.Adj]
    (Cp : H.ConnectedComponent)
    [∀ z : ↥Cp, Fintype (Cp.toSimpleGraph.neighborSet z)] (z : ↥Cp) :
    Cp.toSimpleGraph.degree z ≤ H.degree z.1 := by sorry
