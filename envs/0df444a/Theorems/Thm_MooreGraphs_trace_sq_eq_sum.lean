-- Prove2me | Theorems.Thm_MooreGraphs_trace_sq_eq_sum
-- name    : MooreGraphs.trace_sq_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:24:13.577181+00:00
-- url     : https://prove2.me/theorems/828be205-2984-46bf-ad3e-e8ec46eebcdd
-- title:
--   Moore Graphs: trace sq eq sum
-- statement:
--   The Moore Graphs construction uses the trace sq eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L187-L192
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L187-L192

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

theorem MooreGraphs.trace_sq_eq_sum {W : Type*} [Fintype W] [DecidableEq W] {A : Matrix W W ℝ}
    (hA : A.IsHermitian) : (A ^ 2).trace = ∑ i, hA.eigenvalues i ^ 2 := by sorry
