-- Prove2me | Theorems.Thm_HoffmanSingleton_card_eq
-- name    : HoffmanSingleton.card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:37:34.659543+00:00
-- url     : https://prove2.me/theorems/c8330849-74e4-4d63-9ecf-b8c07e694f1c
-- title:
--   Hoffman Singleton: card eq
-- statement:
--   A finite `k`-regular graph of diameter at most two and girth at least five has exactly
--   `k ^ 2 + 1` vertices.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean#L39-L41
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean#L39-L41

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
public import Definitions.Def_MooreGraphsHoffmanSingleton_Solution
public import Theorems.Thm_MooreGraphs_card_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

theorem HoffmanSingleton.card_eq {k : ℕ} (hreg : G.IsRegularOfDegree k) (hdiam : G.ediam ≤ 2)
    (hgirth : 5 ≤ G.egirth) : Fintype.card V = k ^ 2 + 1 := by sorry
