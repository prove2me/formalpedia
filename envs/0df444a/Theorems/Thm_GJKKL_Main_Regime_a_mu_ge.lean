-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_a_mu_ge
-- name    : GJKKL.Main.Regime.a_mu_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:21.338078+00:00
-- url     : https://prove2.me/theorems/38c1eaeb-4894-48ef-8622-bc1a3019d581
-- title:
--   Regime: a mu ge
-- statement:
--   `16k ≤ aµ` with `a = n/k`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L219-L232
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L219-L232

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

theorem GJKKL.Main.Regime.a_mu_ge : 16 * (k : ℝ) ≤ n / k * d ^ (-(ε ^ 3)) := by sorry
