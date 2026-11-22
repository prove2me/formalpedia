-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_four_sq_le_k4
-- name    : GJKKL.Main.Regime.four_sq_le_k4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:25.547805+00:00
-- url     : https://prove2.me/theorems/d0e38044-e39c-488e-81db-d4f665da3665
-- title:
--   Regime: four sq le k4
-- statement:
--   The Regime construction uses the four sq le k4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L75-L78
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L75-L78

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

theorem GJKKL.Main.Regime.four_sq_le_k4 : 4 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by sorry
