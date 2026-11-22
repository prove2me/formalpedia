-- Prove2me | Theorems.Thm_GJKKL_card_greedySeq_le
-- name    : GJKKL.card_greedySeq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:43.668177+00:00
-- url     : https://prove2.me/theorems/e45c744b-12ea-470c-9d15-9769003f2417
-- title:
--   GJKKL: card greedy Seq le
-- statement:
--   Each matching with `m` edges has at most `m!` orderings among the greedy sequences.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean#L58-L76
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean#L58-L76

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Greedy_Counting
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical

theorem GJKKL.card_greedySeq_le (H : Finset (Finset V)) (hne : ∀ e ∈ H, e.Nonempty) (m : ℕ) :
    ((hist (Finset V) m).filter (IsGreedySeq H)).card ≤
      m.factorial * (matchingsOfSize H m).card := by sorry
