-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_E_pos
-- name    : GJKKL.Main.Regime.E_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:17.823782+00:00
-- url     : https://prove2.me/theorems/0ecc3263-c26e-4535-92a1-2315d5d495cc
-- title:
--   Regime: E pos
-- statement:
--   The Regime construction uses the E pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L140-L140
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L140-L140

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

theorem GJKKL.Main.Regime.E_pos : 0 < d ^ (1 - ε / 8) := by sorry
