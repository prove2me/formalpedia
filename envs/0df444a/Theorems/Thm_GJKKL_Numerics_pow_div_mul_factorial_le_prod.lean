-- Prove2me | Theorems.Thm_GJKKL_Numerics_pow_div_mul_factorial_le_prod
-- name    : GJKKL.Numerics.pow_div_mul_factorial_le_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:28.097802+00:00
-- url     : https://prove2.me/theorems/9b06fc66-accc-4deb-854e-043d26041315
-- title:
--   Numerics: pow div mul factorial le prod
-- statement:
--   `(a/m)^m · m! ≤ ∏_{i<m} (a - i)` for every natural number `m ≤ a`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L97-L111
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L97-L111

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real

theorem GJKKL.Numerics.pow_div_mul_factorial_le_prod (a : ℝ) (m : ℕ) (hm : (m : ℝ) ≤ a) :
    (a / m) ^ m * m.factorial ≤ ∏ i ∈ range m, (a - i) := by sorry
