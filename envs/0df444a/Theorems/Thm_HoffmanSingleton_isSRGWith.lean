-- Prove2me | Theorems.Thm_HoffmanSingleton_isSRGWith
-- name    : HoffmanSingleton.isSRGWith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:44:12.161077+00:00
-- url     : https://prove2.me/theorems/160e8014-0898-424e-a591-b3ae55155c60
-- title:
--   Hoffman Singleton: is SRGWith
-- statement:
--   A finite `k`-regular graph of diameter at most two and girth at least five is strongly
--   regular with parameters `(k ^ 2 + 1, k, 0, 1)`.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean#L45-L47
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean#L45-L47

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
public import Definitions.Def_MooreGraphsHoffmanSingleton_Solution
public import Theorems.Thm_MooreGraphs_isSRGWith

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

theorem HoffmanSingleton.isSRGWith {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : G.IsSRGWith (k ^ 2 + 1) k 0 1 := by sorry
