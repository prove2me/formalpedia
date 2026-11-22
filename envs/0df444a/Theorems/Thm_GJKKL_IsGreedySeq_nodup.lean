-- Prove2me | Theorems.Thm_GJKKL_IsGreedySeq_nodup
-- name    : GJKKL.IsGreedySeq.nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:44.13841+00:00
-- url     : https://prove2.me/theorems/7e624960-e82f-4209-939a-f2a20265054b
-- title:
--   Is Greedy Seq: nodup
-- statement:
--   The Is Greedy Seq construction uses the nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L203-L208
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L203-L208

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

theorem GJKKL.IsGreedySeq.nodup {H : Finset (Finset V)} (hne : ∀ e ∈ H, e.Nonempty)
    {h : List (Finset V)} (hh : IsGreedySeq H h) : h.Nodup := by sorry
