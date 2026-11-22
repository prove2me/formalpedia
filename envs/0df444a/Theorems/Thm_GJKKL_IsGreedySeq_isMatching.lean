-- Prove2me | Theorems.Thm_GJKKL_IsGreedySeq_isMatching
-- name    : GJKKL.IsGreedySeq.isMatching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:28.776094+00:00
-- url     : https://prove2.me/theorems/2cb0e385-426a-4681-867c-2acdd85ae4f7
-- title:
--   Is Greedy Seq: is Matching
-- statement:
--   The Is Greedy Seq construction uses the is Matching property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L224-L228
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L224-L228

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

theorem GJKKL.IsGreedySeq.isMatching {H : Finset (Finset V)} {h : List (Finset V)}
    (hh : IsGreedySeq H h) : IsMatching h.toFinset := by sorry
