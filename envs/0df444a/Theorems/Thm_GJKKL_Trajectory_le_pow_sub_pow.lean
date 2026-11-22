-- Prove2me | Theorems.Thm_GJKKL_Trajectory_le_pow_sub_pow
-- name    : GJKKL.Trajectory.le_pow_sub_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:20.746051+00:00
-- url     : https://prove2.me/theorems/9425beba-8c34-4dd7-971e-f9bf3cb9b9fa
-- title:
--   Trajectory: le pow sub pow
-- statement:
--   Lower bound for a difference of powers.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L70-L81
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L70-L81

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset

theorem GJKKL.Trajectory.le_pow_sub_pow {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (j : ℕ) :
    (j + 1) * y ^ j * (x - y) ≤ x ^ (j + 1) - y ^ (j + 1) := by sorry
