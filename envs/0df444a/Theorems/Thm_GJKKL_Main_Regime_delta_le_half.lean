-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_delta_le_half
-- name    : GJKKL.Main.Regime.delta_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:56.237009+00:00
-- url     : https://prove2.me/theorems/c88af6f3-9315-4ff2-aabb-03febbee32aa
-- title:
--   Regime: delta le half
-- statement:
--   The Regime construction uses the delta le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L383-L389
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L383-L389

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

theorem GJKKL.Main.Regime.delta_le_half {a : ℝ} {t : ℕ} (hμx : d ^ (-(ε ^ 3)) ≤ pfrac a t) (hx1 : pfrac a t ≤ 1) :
    delta k ε d a t ≤ dhat k d a t / 2 := by sorry
