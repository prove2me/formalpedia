-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_mu_le_eta4
-- name    : GJKKL.Main.Regime.mu_le_eta4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:42.093812+00:00
-- url     : https://prove2.me/theorems/d5299dfd-c4cc-47cd-a3fb-312970b4b9a2
-- title:
--   Regime: mu le eta4
-- statement:
--   The Regime construction uses the mu le eta4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L126-L133
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L126-L133

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

theorem GJKKL.Main.Regime.mu_le_eta4 : d ^ (-(ε ^ 3)) ≤ d ^ (-(ε ^ 4)) := by sorry
