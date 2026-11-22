-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_one_le_d
-- name    : GJKKL.Main.Regime.one_le_d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:57.616325+00:00
-- url     : https://prove2.me/theorems/ca289beb-ff1d-49ed-b66e-29fb270aef12
-- title:
--   Regime: one le d
-- statement:
--   The Regime construction uses the one le d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L62-L62
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L62-L62

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

theorem GJKKL.Main.Regime.one_le_d : 1 ≤ d := by sorry
