-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_E_mul
-- name    : GJKKL.Main.Regime.E_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:03.421129+00:00
-- url     : https://prove2.me/theorems/f7c8479d-2858-4770-b187-ecd1b7385e55
-- title:
--   Regime: E mul
-- statement:
--   The Regime construction uses the E mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L201-L205
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L201-L205

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

theorem GJKKL.Main.Regime.E_mul : d * d ^ (ε / 2) ≤ d ^ (1 - ε / 8) * d ^ (ε - ε ^ 3) := by sorry
