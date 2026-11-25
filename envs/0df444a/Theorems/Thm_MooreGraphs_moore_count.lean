-- Prove2me | Theorems.Thm_MooreGraphs_moore_count
-- name    : MooreGraphs.moore_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:15:48.287491+00:00
-- url     : https://prove2.me/theorems/b90476ab-6708-5813-8d23-eacf02c53855
-- title:
--   Moore Graphs: moore count
-- statement:
--   The Moore Graphs construction uses the moore count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L59-L62
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L59-L62

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MooreGraphs.moore_count (k : ℕ) : 1 + (k + k * (k - 1)) = k ^ 2 + 1 := by sorry
