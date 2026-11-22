-- Prove2me | Theorems.Thm_GJKKL_History_expect_le_of_super
-- name    : GJKKL.History.expect_le_of_super
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:00.36275+00:00
-- url     : https://prove2.me/theorems/2878ca0a-2881-4150-8959-0b33562e66fc
-- title:
--   History: expect le of super
-- statement:
--   A process that does not increase in conditional expectation before time `T` has
--   expectation at most its initial value at time `T`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L133-L141
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean#L133-L141

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

theorem GJKKL.History.expect_le_of_super (Z : List α → ℝ) (T : ℕ)
    (hsuper : ∀ h : List α, h.length < T → ∑ a, κ.K h a * Z (a :: h) ≤ Z h) :
    expect κ T Z ≤ Z [] := by sorry
