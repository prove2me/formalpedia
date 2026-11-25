-- Prove2me | Theorems.Thm_MooreGraphs_exists_common_of_ediam
-- name    : MooreGraphs.exists_common_of_ediam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:15:30.323803+00:00
-- url     : https://prove2.me/theorems/e6082ca3-88c0-5f52-ae20-12bf4ff01a90
-- title:
--   Moore Graphs: exists common of ediam
-- statement:
--   The Moore Graphs construction uses the exists common of ediam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L28-L36
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L28-L36

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [Fintype V] [DecidableRel G.Adj]

theorem MooreGraphs.exists_common_of_ediam {u v : V} (hdiam : G.ediam ≤ 2) (huv : u ≠ v)
    (hadj : ¬G.Adj u v) : ∃ w, G.Adj u w ∧ G.Adj w v := by sorry
