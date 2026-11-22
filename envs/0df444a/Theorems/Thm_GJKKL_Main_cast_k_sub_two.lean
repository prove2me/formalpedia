-- Prove2me | Theorems.Thm_GJKKL_Main_cast_k_sub_two
-- name    : GJKKL.Main.cast_k_sub_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:44.924845+00:00
-- url     : https://prove2.me/theorems/577c59be-a73d-47c1-ad61-a1348141e8f6
-- title:
--   Main: cast k sub two
-- statement:
--   The Main construction uses the cast k sub two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L28-L29
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L28-L29

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory

theorem GJKKL.Main.cast_k_sub_two {k : ℕ} (hk : 2 ≤ k) : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by sorry
