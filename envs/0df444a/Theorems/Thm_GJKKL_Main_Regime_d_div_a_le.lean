-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_d_div_a_le
-- name    : GJKKL.Main.Regime.d_div_a_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:13.663894+00:00
-- url     : https://prove2.me/theorems/22713d0f-a910-4730-8640-60e9b73b8858
-- title:
--   Regime: d div a le
-- statement:
--   `d/a ≤ 2k d^{1-ε}`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L257-L275
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L257-L275

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

theorem GJKKL.Main.Regime.d_div_a_le : d / (n / k) ≤ 2 * k * d ^ (1 - ε) := by sorry
