-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_delta_zero
-- name    : GJKKL.Main.Regime.delta_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:46.118794+00:00
-- url     : https://prove2.me/theorems/1277aff7-55c0-45f0-a837-85ce74a06467
-- title:
--   Regime: delta zero
-- statement:
--   The Regime construction uses the delta zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L406-L406
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L406-L406

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

theorem GJKKL.Main.Regime.delta_zero (a : ℝ) : delta k ε d a 0 = d ^ (1 - ε / 8) := by sorry
