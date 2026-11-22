-- Prove2me | Theorems.Thm_GJKKL_Numerics_prod_range_sub_eq_factorial
-- name    : GJKKL.Numerics.prod_range_sub_eq_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:20.364131+00:00
-- url     : https://prove2.me/theorems/1f6bb283-3999-4308-bb4b-ef4aadb92903
-- title:
--   Numerics: prod range sub eq factorial
-- statement:
--   `∏_{i<m} (m - i) = m!`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L86-L94
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L86-L94

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real

theorem GJKKL.Numerics.prod_range_sub_eq_factorial (m : ℕ) :
    ∏ i ∈ range m, ((m : ℝ) - i) = m.factorial := by sorry
