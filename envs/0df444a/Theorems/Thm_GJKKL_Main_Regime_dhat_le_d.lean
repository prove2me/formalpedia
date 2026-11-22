-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_dhat_le_d
-- name    : GJKKL.Main.Regime.dhat_le_d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:40.198669+00:00
-- url     : https://prove2.me/theorems/945d6599-c882-44f5-9dbd-40a21325763a
-- title:
--   Regime: dhat le d
-- statement:
--   The Regime construction uses the dhat le d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L398-L402
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L398-L402

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

theorem GJKKL.Main.Regime.dhat_le_d {a : ℝ} {t : ℕ} (hx0 : 0 ≤ pfrac a t) (hx1 : pfrac a t ≤ 1) :
    dhat k d a t ≤ d := by sorry
