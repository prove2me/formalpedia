-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_key_E
-- name    : GJKKL.Main.Regime.key_E
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:04.835601+00:00
-- url     : https://prove2.me/theorems/8a5c9543-0435-4be8-b64b-8c44f4a29534
-- title:
--   Regime: key E
-- statement:
--   `2E ≤ d µ^{B+k}`: the error is small even at the end of the process.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L149-L161
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L149-L161

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

theorem GJKKL.Main.Regime.key_E : 2 * d ^ (1 - ε / 8) ≤ d * (d ^ (-(ε ^ 3))) ^ (Bn k + k) := by sorry
