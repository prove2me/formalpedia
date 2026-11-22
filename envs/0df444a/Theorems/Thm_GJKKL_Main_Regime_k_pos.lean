-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_k_pos
-- name    : GJKKL.Main.Regime.k_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:50.991604+00:00
-- url     : https://prove2.me/theorems/00faec02-17dd-449d-8abb-a2d1489f8350
-- title:
--   Regime: k pos
-- statement:
--   The Regime construction uses the k pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L66-L66
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L66-L66

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
public import Theorems.Thm_GJKKL_TrackHyp_k_pos

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R

theorem GJKKL.Main.Regime.k_pos : (0 : ℝ) < k := by sorry
