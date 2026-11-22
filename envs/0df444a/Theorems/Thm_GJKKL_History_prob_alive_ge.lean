-- Prove2me | Theorems.Thm_GJKKL_History_prob_alive_ge
-- name    : GJKKL.History.prob_alive_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:01.052249+00:00
-- url     : https://prove2.me/theorems/7e62b3d1-baed-47da-b96a-552e05ed777f
-- title:
--   History: prob alive ge
-- statement:
--   Survival of the good event for a process that cannot stop at a good state.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean#L73-L93
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean#L73-L93

module
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_History_FirstFailure
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (κ : Kernel α) (G : List α → Prop)

theorem GJKKL.History.prob_alive_ge (hmass : ∀ h, G h → ∑ a, κ.K h a = 1) (T : ℕ) :
    1 - ∑ i ∈ range T, prob κ i (fun h => AliveBefore G h ∧ ¬ G h) ≤
      prob κ T (AliveBefore G) := by sorry
