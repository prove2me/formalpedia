-- Prove2me | Theorems.Thm_GJKKL_isGreedySeq_cons
-- name    : GJKKL.isGreedySeq_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:19.479593+00:00
-- url     : https://prove2.me/theorems/f1f37271-d28c-4e51-96e7-12e6486ce856
-- title:
--   GJKKL: is Greedy Seq cons
-- statement:
--   The GJKKL construction uses the is Greedy Seq cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L160-L161
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L160-L161

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

theorem GJKKL.isGreedySeq_cons {H : Finset (Finset V)} {a : Finset V} {h : List (Finset V)} :
    IsGreedySeq H (a :: h) ↔ IsGreedySeq H h ∧ a ∈ avail H h := by sorry
