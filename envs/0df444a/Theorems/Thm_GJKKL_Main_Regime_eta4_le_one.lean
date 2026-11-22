-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_eta4_le_one
-- name    : GJKKL.Main.Regime.eta4_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:51.801596+00:00
-- url     : https://prove2.me/theorems/6d83c232-82d1-429e-946d-1f09e33736a9
-- title:
--   Regime: eta4 le one
-- statement:
--   The Regime construction uses the eta4 le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L135-L136
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L135-L136

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

theorem GJKKL.Main.Regime.eta4_le_one : d ^ (-(ε ^ 4)) ≤ 1 := by sorry
