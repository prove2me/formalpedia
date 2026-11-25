-- Prove2me | Theorems.Thm_MooreGraphs_no_square
-- name    : MooreGraphs.no_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:15:41.858409+00:00
-- url     : https://prove2.me/theorems/40d859e0-04c0-531a-92b0-a6274c155305
-- title:
--   Moore Graphs: no square
-- statement:
--   The Moore Graphs construction uses the no square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L49-L57
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L49-L57

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

theorem MooreGraphs.no_square (hgirth : 5 ≤ G.egirth) {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : False := by sorry
