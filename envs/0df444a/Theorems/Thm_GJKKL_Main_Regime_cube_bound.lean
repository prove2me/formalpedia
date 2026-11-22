-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_cube_bound
-- name    : GJKKL.Main.Regime.cube_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:44.292799+00:00
-- url     : https://prove2.me/theorems/32b96305-4024-416f-92dd-6be54b8f1577
-- title:
--   Regime: cube bound
-- statement:
--   The Regime construction uses the cube bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L86-L99
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L86-L99

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

theorem GJKKL.Main.Regime.cube_bound : ε ^ 3 * (32 * (k : ℝ) ^ 2 + k) ≤ ε / 16 := by sorry
