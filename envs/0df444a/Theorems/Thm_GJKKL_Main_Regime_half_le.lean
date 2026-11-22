-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_half_le
-- name    : GJKKL.Main.Regime.half_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:52.689719+00:00
-- url     : https://prove2.me/theorems/ff8d90aa-dd5b-48d2-a9b8-7de8d85b50af
-- title:
--   Regime: half le
-- statement:
--   The Regime construction uses the half le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L198-L199
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L198-L199

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R

theorem GJKKL.Main.Regime.half_le : d ^ (ε / 2) ≤ d ^ (ε - ε ^ 3) := by sorry
