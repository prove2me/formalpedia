-- Prove2me | Theorems.Thm_MooreGraphs_card_eq
-- name    : MooreGraphs.card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:20:26.234422+00:00
-- url     : https://prove2.me/theorems/f1ba0a4d-6b53-4dc7-ba29-2767ce8567ac
-- title:
--   Moore Graphs: card eq
-- statement:
--   A finite `k`-regular graph of diameter at most two and girth at least five has exactly
--   `k ^ 2 + 1` vertices.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean#L47-L52
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean#L47-L52

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

theorem MooreGraphs.card_eq {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : Fintype.card V = k ^ 2 + 1 := by sorry
