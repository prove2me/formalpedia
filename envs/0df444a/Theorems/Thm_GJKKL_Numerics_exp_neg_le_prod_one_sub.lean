-- Prove2me | Theorems.Thm_GJKKL_Numerics_exp_neg_le_prod_one_sub
-- name    : GJKKL.Numerics.exp_neg_le_prod_one_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:14.42937+00:00
-- url     : https://prove2.me/theorems/db4d12d0-2828-4e8a-93ed-8ba961f15f00
-- title:
--   Numerics: exp neg le prod one sub
-- statement:
--   `e^{-m} ≤ ∏_{i<m} (1 - i/a)` for every natural number `m ≤ a`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L67-L83
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L67-L83

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real

theorem GJKKL.Numerics.exp_neg_le_prod_one_sub (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : (m : ℝ) ≤ a) :
    exp (-(m : ℝ)) ≤ ∏ i ∈ range m, (1 - (i : ℝ) / a) := by sorry
