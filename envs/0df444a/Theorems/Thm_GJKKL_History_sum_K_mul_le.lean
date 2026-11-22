-- Prove2me | Theorems.Thm_GJKKL_History_sum_K_mul_le
-- name    : GJKKL.History.sum_K_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:53.102792+00:00
-- url     : https://prove2.me/theorems/55ca8d2e-e6e8-48d5-9f00-5c3ccbc10d0e
-- title:
--   History: sum K mul le
-- statement:
--   `Σₐ K h a · f a ≤ c` when `f ≤ c` pointwise and `c ≥ 0`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean#L34-L39
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/FirstFailure.lean#L34-L39

module
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_History_FirstFailure
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (κ : Kernel α) (G : List α → Prop)

theorem GJKKL.History.sum_K_mul_le (h : List α) {f : α → ℝ} {c : ℝ} (hf : ∀ a, f a ≤ c) (hc : 0 ≤ c) :
    ∑ a, κ.K h a * f a ≤ c := by sorry
