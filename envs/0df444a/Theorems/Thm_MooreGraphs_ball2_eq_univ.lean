-- Prove2me | Theorems.Thm_MooreGraphs_ball2_eq_univ
-- name    : MooreGraphs.ball2_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:15:42.570724+00:00
-- url     : https://prove2.me/theorems/33991537-0aef-4745-853e-11771f62ecaf
-- title:
--   Moore Graphs: ball2 eq univ
-- statement:
--   The Moore Graphs construction uses the ball2 eq univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L68-L76
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L68-L76

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MooreGraphs.ball2_eq_univ [DecidableEq V] (hdiam : G.ediam ≤ 2) (v : V) : ball2 G v = univ := by sorry
