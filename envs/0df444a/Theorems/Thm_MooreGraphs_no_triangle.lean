-- Prove2me | Theorems.Thm_MooreGraphs_no_triangle
-- name    : MooreGraphs.no_triangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:15:36.298838+00:00
-- url     : https://prove2.me/theorems/64abf9ca-0af5-5ff4-b6f6-ab2bbc92c4fc
-- title:
--   Moore Graphs: no triangle
-- statement:
--   The Moore Graphs construction uses the no triangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L39-L46
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L39-L46

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

theorem MooreGraphs.no_triangle (hgirth : 5 ≤ G.egirth) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) : False := by sorry
