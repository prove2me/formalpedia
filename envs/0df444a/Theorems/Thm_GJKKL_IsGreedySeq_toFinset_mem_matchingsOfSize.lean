-- Prove2me | Theorems.Thm_GJKKL_IsGreedySeq_toFinset_mem_matchingsOfSize
-- name    : GJKKL.IsGreedySeq.toFinset_mem_matchingsOfSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:24.096625+00:00
-- url     : https://prove2.me/theorems/6609ade6-2021-47ed-aa22-b89534494f86
-- title:
--   Is Greedy Seq: to Finset mem matchings Of Size
-- statement:
--   A greedy sequence of length `m` is an ordering of a matching of `H` with `m` edges.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L231-L236
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L231-L236

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

theorem GJKKL.IsGreedySeq.toFinset_mem_matchingsOfSize {H : Finset (Finset V)}
    (hne : ∀ e ∈ H, e.Nonempty) {h : List (Finset V)} (hh : IsGreedySeq H h) :
    h.toFinset ∈ matchingsOfSize H h.length := by sorry
