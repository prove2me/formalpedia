-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_a_mu_E_ge
-- name    : GJKKL.Main.Regime.a_mu_E_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:57.842311+00:00
-- url     : https://prove2.me/theorems/5ade637d-8fb4-40c0-871a-7752a4537109
-- title:
--   Regime: a mu E ge
-- statement:
--   `d ≤ aµE`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L235-L254
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L235-L254

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
variable {n : ℝ} (hn : ((k : ℝ) - 1) * d ^ ε / 2 ≤ n)
include hn

theorem GJKKL.Main.Regime.a_mu_E_ge : d ≤ n / k * d ^ (-(ε ^ 3)) * d ^ (1 - ε / 8) := by sorry
