-- Prove2me | Theorems.Thm_HoffmanSingleton_card_le
-- name    : HoffmanSingleton.card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:37:24.623003+00:00
-- url     : https://prove2.me/theorems/20494183-a88b-4484-9f75-e746847a8a19
-- title:
--   Hoffman Singleton: card le
-- statement:
--   **Moore bound.** A finite `k`-regular graph of diameter at most two has at most `k ^ 2 + 1`
--   vertices.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean#L33-L35
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean#L33-L35

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
public import Definitions.Def_MooreGraphsHoffmanSingleton_Solution
public import Theorems.Thm_MooreGraphs_card_le

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

theorem HoffmanSingleton.card_le {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2) :
    Fintype.card V ≤ k ^ 2 + 1 := by sorry
