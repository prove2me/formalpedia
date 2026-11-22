-- Prove2me | Theorems.Thm_GJKKL_Trajectory_inv_pow_sub_inv_pow_ge
-- name    : GJKKL.Trajectory.inv_pow_sub_inv_pow_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:37.055603+00:00
-- url     : https://prove2.me/theorems/836a36e4-38b0-4fe4-a5e0-0d76d2c8f551
-- title:
--   Trajectory: inv pow sub inv pow ge
-- statement:
--   Lower bound for the growth of `1/p^B`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L84-L107
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L84-L107

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset

theorem GJKKL.Trajectory.inv_pow_sub_inv_pow_ge {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) (B : ℕ) :
    (B : ℝ) * (x - y) / x ^ (B + 1) ≤ 1 / y ^ B - 1 / x ^ B := by sorry
