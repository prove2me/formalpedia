-- Prove2me | Theorems.Thm_GJKKL_Trajectory_pfrac_sub_succ
-- name    : GJKKL.Trajectory.pfrac_sub_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:32.077436+00:00
-- url     : https://prove2.me/theorems/2a64d1a6-7add-4847-ac3d-ccb66490c1ec
-- title:
--   Trajectory: pfrac sub succ
-- statement:
--   The Trajectory construction uses the pfrac sub succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L35-L36
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L35-L36

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset

theorem GJKKL.Trajectory.pfrac_sub_succ (a : ℝ) (t : ℕ) : pfrac a t - pfrac a (t + 1) = 1 / a := by sorry
