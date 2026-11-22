-- Prove2me | Theorems.Thm_GJKKL_Trajectory_pfrac_le_one
-- name    : GJKKL.Trajectory.pfrac_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:25.670368+00:00
-- url     : https://prove2.me/theorems/c6db39e6-c2cf-4a4c-ab59-a9b077a78185
-- title:
--   Trajectory: pfrac le one
-- statement:
--   The Trajectory construction uses the pfrac le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L38-L41
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L38-L41

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset

theorem GJKKL.Trajectory.pfrac_le_one {a : ℝ} (ha : 0 ≤ a) (t : ℕ) : pfrac a t ≤ 1 := by sorry
