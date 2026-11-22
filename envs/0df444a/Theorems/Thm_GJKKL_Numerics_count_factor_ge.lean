-- Prove2me | Theorems.Thm_GJKKL_Numerics_count_factor_ge
-- name    : GJKKL.Numerics.count_factor_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:35.567784+00:00
-- url     : https://prove2.me/theorems/b03ab14f-692e-40a7-a1bc-7f9e348dd521
-- title:
--   Numerics: count factor ge
-- statement:
--   The factor of the final count: for natural numbers `m ≤ a` and `j`,
--   `e^{-jm} (a/m)^m ≤ a^m (∏_{i<m} (1 - i/a))^{j+1} / m!`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L115-L136
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L115-L136

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real

theorem GJKKL.Numerics.count_factor_ge (a : ℝ) (ha : 0 < a) (m j : ℕ) (hm : (m : ℝ) ≤ a) :
    exp (-((j : ℝ) * m)) * (a / m) ^ m ≤
      a ^ m * (∏ i ∈ range m, (1 - (i : ℝ) / a)) ^ (j + 1) / m.factorial := by sorry
