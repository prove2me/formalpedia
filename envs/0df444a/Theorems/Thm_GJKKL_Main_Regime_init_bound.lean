-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_init_bound
-- name    : GJKKL.Main.Regime.init_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:20.404911+00:00
-- url     : https://prove2.me/theorems/6ef4ac94-449c-453b-a0e6-c61cf5e8b896
-- title:
--   Regime: init bound
-- statement:
--   The Regime construction uses the init bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L163-L167
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L163-L167

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

theorem GJKKL.Main.Regime.init_bound : 2 * d ^ (1 - ε) ≤ d ^ (1 - ε / 8) := by sorry
