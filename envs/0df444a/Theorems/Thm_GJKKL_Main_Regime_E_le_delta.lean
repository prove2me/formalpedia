-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_E_le_delta
-- name    : GJKKL.Main.Regime.E_le_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:28.783794+00:00
-- url     : https://prove2.me/theorems/3bfe4525-4b15-4c78-b586-51a11c232756
-- title:
--   Regime: E le delta
-- statement:
--   The Regime construction uses the E le delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L391-L396
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L391-L396

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

theorem GJKKL.Main.Regime.E_le_delta {a : ℝ} {t : ℕ} (hx0 : 0 < pfrac a t) (hx1 : pfrac a t ≤ 1) :
    d ^ (1 - ε / 8) ≤ delta k ε d a t := by sorry
