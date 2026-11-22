-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_k_ge
-- name    : GJKKL.Main.Regime.k_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:18.306827+00:00
-- url     : https://prove2.me/theorems/ef6c5975-9e3d-4b15-9924-6b83a7b01c14
-- title:
--   Regime: k ge
-- statement:
--   The Regime construction uses the k ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L64-L64
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L64-L64

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

theorem GJKKL.Main.Regime.k_ge : (2 : ℝ) ≤ k := by sorry
