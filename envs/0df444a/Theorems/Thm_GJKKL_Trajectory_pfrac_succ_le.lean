-- Prove2me | Theorems.Thm_GJKKL_Trajectory_pfrac_succ_le
-- name    : GJKKL.Trajectory.pfrac_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:07.733892+00:00
-- url     : https://prove2.me/theorems/450350c1-b1d8-4bc2-b06c-614ed6c9bf06
-- title:
--   Trajectory: pfrac succ le
-- statement:
--   The Trajectory construction uses the pfrac succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L43-L46
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L43-L46

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset

theorem GJKKL.Trajectory.pfrac_succ_le (a : ℝ) (ha : 0 ≤ a) (t : ℕ) : pfrac a (t + 1) ≤ pfrac a t := by sorry
