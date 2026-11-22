-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_two_E_le
-- name    : GJKKL.Main.Regime.two_E_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:30.521109+00:00
-- url     : https://prove2.me/theorems/bf165be2-178a-487f-b2c9-ee688fa4fcca
-- title:
--   Regime: two E le
-- statement:
--   The error bound `2E ≤ µ d x^{B+k-1}` for `µ ≤ x ≤ 1`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L359-L372
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L359-L372

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

theorem GJKKL.Main.Regime.two_E_le {x : ℝ} (hμx : d ^ (-(ε ^ 3)) ≤ x) (hx1 : x ≤ 1) :
    2 * d ^ (1 - ε / 8) ≤ d ^ (-(ε ^ 3)) * d * x ^ (Bn k + (k - 1)) := by sorry
