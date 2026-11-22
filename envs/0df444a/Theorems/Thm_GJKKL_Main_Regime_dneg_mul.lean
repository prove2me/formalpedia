-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_dneg_mul
-- name    : GJKKL.Main.Regime.dneg_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:35.259992+00:00
-- url     : https://prove2.me/theorems/e1734299-0405-4c89-9afa-6558caeaf31a
-- title:
--   Regime: dneg mul
-- statement:
--   The Regime construction uses the dneg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L178-L180
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L178-L180

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

theorem GJKKL.Main.Regime.dneg_mul : d ^ (-ε) * d = d ^ (1 - ε) := by sorry
