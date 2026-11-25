-- Prove2me | Theorems.Thm_HoffmanSingleton_hoffman_singleton
-- name    : HoffmanSingleton.hoffman_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:48:45.339124+00:00
-- url     : https://prove2.me/theorems/f7b9687f-2b0b-507a-818e-2a5e60b106c5
-- title:
--   Hoffman Singleton: hoffman singleton
-- statement:
--   **Hoffman–Singleton theorem (1960).** If a finite `k`-regular graph with `k ≥ 2` has diameter
--   at most two and girth at least five (a Moore graph of diameter two), then
--   `k ∈ {2, 3, 7, 57}`.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean#L52-L54
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean#L52-L54

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
public import Definitions.Def_MooreGraphsHoffmanSingleton_Solution
public import Theorems.Thm_MooreGraphs_hoffman_singleton

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

theorem HoffmanSingleton.hoffman_singleton {k : ℕ} (hk : 2 ≤ k) (hreg : G.IsRegularOfDegree k)
    (hdiam : G.ediam ≤ 2) (hgirth : 5 ≤ G.egirth) : k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by sorry
