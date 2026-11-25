-- Prove2me | Theorems.Thm_MooreGraphs_isSRGWith
-- name    : MooreGraphs.isSRGWith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:20:47.371329+00:00
-- url     : https://prove2.me/theorems/4f3b07c8-ebe5-4035-8396-7e7a156fdef3
-- title:
--   Moore Graphs: is SRGWith
-- statement:
--   A finite `k`-regular graph of diameter at most two and girth at least five is strongly
--   regular with parameters `(k ^ 2 + 1, k, 0, 1)`.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean#L56-L69
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean#L56-L69

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

theorem MooreGraphs.isSRGWith {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : G.IsSRGWith (k ^ 2 + 1) k 0 1 := by sorry
