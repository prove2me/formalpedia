-- Prove2me | Theorems.Thm_GJKKL_History_exp_step_le_super
-- name    : GJKKL.History.exp_step_le_super
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:26.4086+00:00
-- url     : https://prove2.me/theorems/97efe9ea-1170-49a7-a613-82c37643cc4e
-- title:
--   History: exp step le super
-- statement:
--   One step of the exponential supermartingale, for a sub-probability law and a
--   non-positive mean increment.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L44-L79
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L44-L79

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset

theorem GJKKL.History.exp_step_le_super {β : Type*} [Fintype β] (p : β → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a ≤ 1) (Δ : β → ℝ) (hmean : ∑ a, p a * Δ a ≤ 0) (C θ : ℝ) (hθ : 0 ≤ θ)
    (hθC : θ * C < 1) (hΔ : ∀ a, p a ≠ 0 → |Δ a| ≤ C) :
    ∑ a, p a * Real.exp (θ * Δ a) ≤
      Real.exp (θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a|) := by sorry
