-- Prove2me | Theorems.Thm_GJKKL_History_mul_prob_le_expect
-- name    : GJKKL.History.mul_prob_le_expect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:22.954681+00:00
-- url     : https://prove2.me/theorems/62352676-0449-4eb4-a5fd-ce79c62f46de
-- title:
--   History: mul prob le expect
-- statement:
--   Markov's inequality: if `c ≤ Z` on the event and `0 ≤ Z` everywhere, then
--   `c · P[event] ≤ E[Z]`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L205-L214
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L205-L214

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)

theorem GJKKL.History.mul_prob_le_expect {T : ℕ} {P : List α → Prop} {Z : List α → ℝ} {c : ℝ}
    (hZ : ∀ h, h.length = T → 0 ≤ Z h) (hcZ : ∀ h, h.length = T → P h → c ≤ Z h) :
    c * prob κ T P ≤ expect κ T Z := by sorry
