-- Prove2me | Theorems.Thm_GJKKL_weight_eq_zero_of_not
-- name    : GJKKL.weight_eq_zero_of_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:18.429051+00:00
-- url     : https://prove2.me/theorems/5ed30a25-892a-4291-bd85-899023c3cf9b
-- title:
--   GJKKL: weight eq zero of not
-- statement:
--   The GJKKL construction uses the weight eq zero of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L182-L186
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L182-L186

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

theorem GJKKL.weight_eq_zero_of_not {H : Finset (Finset V)} {h : List (Finset V)}
    (hh : ¬ IsGreedySeq H h) : weight (greedyKernel H) h = 0 := by sorry
