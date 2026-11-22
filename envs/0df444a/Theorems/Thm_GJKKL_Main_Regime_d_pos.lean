-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_d_pos
-- name    : GJKKL.Main.Regime.d_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:26.06532+00:00
-- url     : https://prove2.me/theorems/4d3e43db-1906-41ec-950d-c4901e544151
-- title:
--   Regime: d pos
-- statement:
--   The Regime construction uses the d pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L60-L60
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L60-L60

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

theorem GJKKL.Main.Regime.d_pos : 0 < d := by sorry
