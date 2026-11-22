-- Prove2me | Theorems.Thm_GJKKL_Trajectory_pfrac_antitone
-- name    : GJKKL.Trajectory.pfrac_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:11:21.55684+00:00
-- url     : https://prove2.me/theorems/de0b3ec2-ee88-456f-8a0d-aaf3a27db04f
-- title:
--   Trajectory: pfrac antitone
-- statement:
--   The Trajectory construction uses the pfrac antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L48-L52
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean#L48-L52

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Functions
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
open Finset

theorem GJKKL.Trajectory.pfrac_antitone {a : ℝ} (ha : 0 ≤ a) {s t : ℕ} (hst : s ≤ t) :
    pfrac a t ≤ pfrac a s := by sorry
