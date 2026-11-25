-- Prove2me | Theorems.Thm_MooreGraphs_adjMatrix_sq_add_eq
-- name    : MooreGraphs.adjMatrix_sq_add_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:16:19.715584+00:00
-- url     : https://prove2.me/theorems/1be56647-195e-4662-a42c-83266fda42a3
-- title:
--   Moore Graphs: adj Matrix sq add eq
-- statement:
--   The Moore Graphs construction uses the adj Matrix sq add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L156-L163
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L156-L163

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MooreGraphs.adjMatrix_sq_add_eq [DecidableEq V] {n k : ℕ} (hsrg : G.IsSRGWith n k 0 1) :
    adjMatrix ℝ G ^ 2 + adjMatrix ℝ G - ((k : ℝ) - 1) • (1 : Matrix V V ℝ) =
      Matrix.of fun _ _ => 1 := by sorry
