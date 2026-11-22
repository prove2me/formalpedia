-- Prove2me | Theorems.Thm_GJKKL_card_avail_both_le_codegree
-- name    : GJKKL.card_avail_both_le_codegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:45.790797+00:00
-- url     : https://prove2.me/theorems/c8269f38-bb56-44f6-9e2b-a25c81ab88ce
-- title:
--   GJKKL: card avail both le codegree
-- statement:
--   The GJKKL construction uses the card avail both le codegree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L81-L83
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L81-L83

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.card_avail_both_le_codegree (H : Finset (Finset V)) (h : List (Finset V)) (u w : V) :
    ((avail H h).filter (fun e => u ∈ e ∧ w ∈ e)).card ≤ codegree H u w := by sorry
