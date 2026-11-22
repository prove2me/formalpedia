-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_E_le_d
-- name    : GJKKL.Main.Regime.E_le_d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:52.071743+00:00
-- url     : https://prove2.me/theorems/9b4a3725-7a91-477b-bab2-a64459ab5b00
-- title:
--   Regime: E le d
-- statement:
--   The Regime construction uses the E le d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L142-L144
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L142-L144

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

theorem GJKKL.Main.Regime.E_le_d : d ^ (1 - ε / 8) ≤ d := by sorry
