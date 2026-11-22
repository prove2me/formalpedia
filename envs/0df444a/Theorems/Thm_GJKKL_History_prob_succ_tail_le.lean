-- Prove2me | Theorems.Thm_GJKKL_History_prob_succ_tail_le
-- name    : GJKKL.History.prob_succ_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:24.254295+00:00
-- url     : https://prove2.me/theorems/9e551f07-5ad1-4f24-b837-9b81d052bc7d
-- title:
--   History: prob succ tail le
-- statement:
--   `P_{T+1}[E ∘ tail] ≤ P_T[E]`: the probability of an event about the previous state.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean#L42-L49
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean#L42-L49

module
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_History_FirstFailure
public import Theorems.Thm_Pseudorandom_CoordGap_tail
public import Theorems.Thm_Pseudorandom_CoordRare_tail
public import Theorems.Thm_Pseudorandom_IsPMF_tail

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (κ : Kernel α) (G : List α → Prop)

theorem GJKKL.History.prob_succ_tail_le (T : ℕ) (E : List α → Prop) :
    prob κ (T + 1) (fun h => E h.tail) ≤ prob κ T E := by sorry
