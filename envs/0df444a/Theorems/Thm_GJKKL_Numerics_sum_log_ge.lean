-- Prove2me | Theorems.Thm_GJKKL_Numerics_sum_log_ge
-- name    : GJKKL.Numerics.sum_log_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:12.577942+00:00
-- url     : https://prove2.me/theorems/8e8eeecd-5843-4795-a9ed-7179429e9b78
-- title:
--   Numerics: sum log ge
-- statement:
--   `F(m) ≤ Σ_{i<m} log(1 - i/a)` with `F(t) = -(a - t) log((a - t)/a) - t`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L53-L64
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L53-L64

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real

theorem GJKKL.Numerics.sum_log_ge (a : ℝ) (ha : 0 < a) :
    ∀ m : ℕ, (m : ℝ) ≤ a →
      -(a - m) * log ((a - m) / a) - m ≤ ∑ i ∈ range m, log ((a - i) / a)
  := by sorry
