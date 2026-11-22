-- Prove2me | Theorems.Thm_GJKKL_Numerics_tangent_step
-- name    : GJKKL.Numerics.tangent_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:07.681116+00:00
-- url     : https://prove2.me/theorems/eab2eb35-4c0a-4e36-9cbc-866756734742
-- title:
--   Numerics: tangent step
-- statement:
--   The tangent-line step: `(u - 1) log(u / (u - 1)) ≤ 1` in the form used below.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L33-L50
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Numerics/Falling.lean#L33-L50

module
public import Mathlib
public import Definitions.Def_GJKKL_Numerics_Falling
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Numerics
open Finset Real

theorem GJKKL.Numerics.tangent_step {a u : ℝ} (ha : 0 < a) (hu : 1 ≤ u) :
    u * log (u / a) - (u - 1) * log ((u - 1) / a) - 1 ≤ log (u / a) := by sorry
