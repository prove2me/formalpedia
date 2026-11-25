-- Prove2me | Theorems.Thm_MooreGraphs_final_arith
-- name    : MooreGraphs.final_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:16:01.717049+00:00
-- url     : https://prove2.me/theorems/6063493a-70a2-5911-9228-213dbdab9989
-- title:
--   Moore Graphs: final arith
-- statement:
--   The Moore Graphs construction uses the final arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L122-L154
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean#L122-L154

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MooreGraphs.final_arith {k : ℕ} (hk : 2 ≤ k) (d : ℤ) (h : (d : ℝ) * √(4 * k - 3) = k ^ 2 - 2 * k) :
    k = 2 ∨ k = 3 ∨ k = 7 ∨ k = 57 := by sorry
