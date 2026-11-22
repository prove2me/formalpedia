-- Prove2me | Theorems.Thm_GJKKL_weight_pos_iff
-- name    : GJKKL.weight_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:11.304413+00:00
-- url     : https://prove2.me/theorems/b22d80e7-0a71-43ed-b99e-5e66e34844b8
-- title:
--   GJKKL: weight pos iff
-- statement:
--   The GJKKL construction uses the weight pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L168-L180
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L168-L180

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

theorem GJKKL.weight_pos_iff {H : Finset (Finset V)} :
    ∀ {h : List (Finset V)}, 0 < weight (greedyKernel H) h ↔ IsGreedySeq H h
  := by sorry
