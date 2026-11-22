-- Prove2me | Theorems.Thm_GJKKL_Trajectory_inv_pow_sub_inv_pow_le
-- name    : GJKKL.Trajectory.inv_pow_sub_inv_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:42.041794+00:00
-- url     : https://prove2.me/theorems/3d96c2c2-84ac-4ddd-b68d-379ac6cce86c
-- title:
--   Trajectory: inv pow sub inv pow le
-- statement:
--   Upper bound for the growth of `1/p^B`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L110-L126
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L110-L126

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset

theorem GJKKL.Trajectory.inv_pow_sub_inv_pow_le {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) (B : ℕ) :
    1 / y ^ B - 1 / x ^ B ≤ (B : ℝ) * (x - y) / (x * y ^ B) := by sorry
