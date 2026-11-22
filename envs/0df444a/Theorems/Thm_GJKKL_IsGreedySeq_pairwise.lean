-- Prove2me | Theorems.Thm_GJKKL_IsGreedySeq_pairwise
-- name    : GJKKL.IsGreedySeq.pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:39.761863+00:00
-- url     : https://prove2.me/theorems/39d42e58-70d2-4858-befd-71a25870461e
-- title:
--   Is Greedy Seq: pairwise
-- statement:
--   The Is Greedy Seq construction uses the pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L197-L201
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L197-L201

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.IsGreedySeq.pairwise {H : Finset (Finset V)} :
    ∀ {h : List (Finset V)}, IsGreedySeq H h → h.Pairwise Disjoint
  := by sorry
