-- Prove2me | Theorems.Thm_MooreGraphs_card_ball2_le
-- name    : MooreGraphs.card_ball2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:15:54.982824+00:00
-- url     : https://prove2.me/theorems/80c67994-e2db-5ed4-aced-351c30cdff2b
-- title:
--   Moore Graphs: card ball2 le
-- statement:
--   The Moore Graphs construction uses the card ball2 le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L78-L92
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L78-L92

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MooreGraphs.card_ball2_le [DecidableEq V] {k : ℕ} (hreg : G.IsRegularOfDegree k) (v : V) :
    (ball2 G v).card ≤ k ^ 2 + 1 := by sorry
