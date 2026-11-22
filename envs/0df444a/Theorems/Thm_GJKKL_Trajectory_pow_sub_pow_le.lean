-- Prove2me | Theorems.Thm_GJKKL_Trajectory_pow_sub_pow_le
-- name    : GJKKL.Trajectory.pow_sub_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:04.448576+00:00
-- url     : https://prove2.me/theorems/18d0aae6-6725-4dfb-a50e-b0aed386777d
-- title:
--   Trajectory: pow sub pow le
-- statement:
--   Upper bound for a difference of powers.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L55-L67
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L55-L67

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset

theorem GJKKL.Trajectory.pow_sub_pow_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (j : ℕ) :
    x ^ (j + 1) - y ^ (j + 1) ≤ (j + 1) * x ^ j * (x - y) := by sorry
