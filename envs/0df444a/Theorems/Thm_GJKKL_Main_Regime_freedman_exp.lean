-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_freedman_exp
-- name    : GJKKL.Main.Regime.freedman_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:26.9404+00:00
-- url     : https://prove2.me/theorems/e32650b4-2c7b-4ec1-ae41-d36d2dcaf832
-- title:
--   Regime: freedman exp
-- statement:
--   The Regime construction uses the freedman exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L182-L186
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L182-L186

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

theorem GJKKL.Main.Regime.freedman_exp : 19200 * (k : ℝ) ^ 4 * d ^ (ε ^ 3) ≤ d ^ (3 * ε / 4) := by sorry
