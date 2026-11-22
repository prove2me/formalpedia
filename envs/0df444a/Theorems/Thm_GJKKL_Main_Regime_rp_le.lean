-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_rp_le
-- name    : GJKKL.Main.Regime.rp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:38.368827+00:00
-- url     : https://prove2.me/theorems/41168bd3-57fa-49fb-91f9-c0db02d3adbc
-- title:
--   Regime: rp le
-- statement:
--   The Regime construction uses the rp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L109-L109
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L109-L109

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

theorem GJKKL.Main.Regime.rp_le {x y : ℝ} (h : x ≤ y) : d ^ x ≤ d ^ y := by sorry
