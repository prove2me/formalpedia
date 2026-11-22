-- Prove2me | Theorems.Thm_GJKKL_History_prob_not_alive_le
-- name    : GJKKL.History.prob_not_alive_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:28.485148+00:00
-- url     : https://prove2.me/theorems/90087f36-37b8-462e-a524-a983345b021c
-- title:
--   History: prob not alive le
-- statement:
--   The History construction uses the prob not alive le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean#L51-L70
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean#L51-L70

module
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_History_FirstFailure
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (κ : Kernel α) (G : List α → Prop)

theorem GJKKL.History.prob_not_alive_le (T : ℕ) :
    prob κ T (fun h => ¬ AliveBefore G h) ≤
      ∑ i ∈ range T, prob κ i (fun h => AliveBefore G h ∧ ¬ G h) := by sorry
