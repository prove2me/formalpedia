-- Prove2me | Theorems.Thm_MooreGraphs_card_ball2_eq
-- name    : MooreGraphs.card_ball2_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:16:02.216451+00:00
-- url     : https://prove2.me/theorems/02599b22-038e-4e92-a001-49b07eaf76c0
-- title:
--   Moore Graphs: card ball2 eq
-- statement:
--   The Moore Graphs construction uses the card ball2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L94-L120
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L94-L120

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MooreGraphs.card_ball2_eq [DecidableEq V] {k : ℕ} (hreg : G.IsRegularOfDegree k)
    (hgirth : 5 ≤ G.egirth) (v : V) : (ball2 G v).card = k ^ 2 + 1 := by sorry
