-- Prove2me | Theorems.Thm_NashWilliams_not_reachable_deleteEdges_of_mem_edges
-- name    : NashWilliams.not_reachable_deleteEdges_of_mem_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:51:09.453522+00:00
-- url     : https://prove2.me/theorems/98fa92e0-3d18-4417-8ddb-923c294e417b
-- title:
--   Nash Williams: not reachable delete Edges of mem edges
-- statement:
--   Deleting an edge of the unique path between `u` and `v` in a forest disconnects `u` from
--   `v`.
--
--   Source: https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L155-L165
-- source:
--   https://github.com/jtraverso/nash-williams-trees/blob/101e48847a929dd8102521f57723e2137989ce2e/TreePackingLib/NashWilliamsAux.lean#L155-L165

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}

theorem NashWilliams.not_reachable_deleteEdges_of_mem_edges {F : SimpleGraph V} (hF : F.IsAcyclic) {u v x y : V}
    (p : F.Walk u v) (hp : p.IsPath) (he : s(x, y) ∈ p.edges) :
    ¬ (F.deleteEdges {s(x, y)}).Reachable u v := by sorry
