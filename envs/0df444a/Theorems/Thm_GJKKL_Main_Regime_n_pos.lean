-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_n_pos
-- name    : GJKKL.Main.Regime.n_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:46.251109+00:00
-- url     : https://prove2.me/theorems/31fe822e-4e3c-4cc2-86e8-1e7327165213
-- title:
--   Regime: n pos
-- statement:
--   The Regime construction uses the n pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L214-L216
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L214-L216

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
variable {n : ℝ} (hn : ((k : ℝ) - 1) * d ^ ε / 2 ≤ n)
include hn

theorem GJKKL.Main.Regime.n_pos : 0 < n := by sorry
