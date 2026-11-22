-- Prove2me | Theorems.Thm_GJKKL_IsGreedySeq_subset
-- name    : GJKKL.IsGreedySeq.subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:36.607808+00:00
-- url     : https://prove2.me/theorems/91b4fd61-d5be-4a3a-bcfd-244cc96c268d
-- title:
--   Is Greedy Seq: subset
-- statement:
--   The Is Greedy Seq construction uses the subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L188-L195
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L188-L195

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

theorem GJKKL.IsGreedySeq.subset {H : Finset (Finset V)} :
    ∀ {h : List (Finset V)}, IsGreedySeq H h → ∀ f ∈ h, f ∈ H
  := by sorry
