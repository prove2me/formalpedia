-- Prove2me | Theorems.Thm_MooreGraphs_hoffman_singleton
-- name    : MooreGraphs.hoffman_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:21:01.096941+00:00
-- url     : https://prove2.me/theorems/7cb3ad02-3474-4a5c-af65-7d5c4903d1f1
-- title:
--   Moore Graphs: hoffman singleton
-- statement:
--   **Hoffman–Singleton theorem (1960).** If a finite `k`-regular graph with `k ≥ 2` has diameter
--   at most two and girth at least five (a Moore graph of diameter two), then
--   `k ∈ {2, 3, 7, 57}`.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean#L74-L129
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean#L74-L129

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Definitions.Def_MooreLib_MooreGraphs
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open MooreGraphs
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

theorem MooreGraphs.hoffman_singleton {k : ℕ} (hk : 2 ≤ k) (hreg : G.IsRegularOfDegree k)
    (hdiam : G.ediam ≤ 2) (hgirth : 5 ≤ G.egirth) : k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by sorry
