-- Prove2me | Theorems.Thm_MooreGraphs_card_le
-- name    : MooreGraphs.card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:20:20.122007+00:00
-- url     : https://prove2.me/theorems/fbbe6fa3-29cf-5f62-b4bf-ddd84f4a3cbf
-- title:
--   Moore Graphs: card le
-- statement:
--   **Moore bound.** A finite `k`-regular graph of diameter at most two has at most `k ^ 2 + 1`
--   vertices.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean#L38-L43
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean#L38-L43

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

theorem MooreGraphs.card_le {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2) :
    Fintype.card V ≤ k ^ 2 + 1 := by sorry
