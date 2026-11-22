-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_union_small
-- name    : GJKKL.Main.Regime.union_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:25.977796+00:00
-- url     : https://prove2.me/theorems/937213c6-8b22-486a-8c5f-d246b86fd8ec
-- title:
--   Regime: union small
-- statement:
--   The failure probability is at most `1/2`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L422-L488
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L422-L488

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
set_option maxHeartbeats 800000

theorem GJKKL.Main.Regime.union_small {n T : ℕ} (hT : T ≤ n) (hn : (n : ℝ) ≤ Real.exp (d ^ (ε ^ 3))) :
    (T : ℝ) * (2 * n) * Real.exp (-((d ^ (1 - ε / 8) / 2) ^ 2 /
      (2 * (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) * (d ^ (1 - ε / 8) / 2 + 5 * k * d)))) ≤ 1 / 2 := by sorry
