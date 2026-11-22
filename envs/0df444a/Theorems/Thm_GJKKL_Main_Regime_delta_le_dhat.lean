-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_delta_le_dhat
-- name    : GJKKL.Main.Regime.delta_le_dhat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:35.731538+00:00
-- url     : https://prove2.me/theorems/ad7ee381-30a3-4f93-a10d-33269bfbe202
-- title:
--   Regime: delta le dhat
-- statement:
--   The Regime construction uses the delta le dhat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L374-L381
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L374-L381

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

theorem GJKKL.Main.Regime.delta_le_dhat {a : ℝ} {t : ℕ} (hμx : d ^ (-(ε ^ 3)) ≤ pfrac a t) (hx1 : pfrac a t ≤ 1) :
    delta k ε d a t ≤ d ^ (-(ε ^ 3)) / 2 * dhat k d a t := by sorry
