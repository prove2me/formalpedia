-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_x_pos
-- name    : GJKKL.Main.Regime.x_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:47.970929+00:00
-- url     : https://prove2.me/theorems/4e74df73-638d-4d1a-8d41-abec7cdb4465
-- title:
--   Regime: x pos
-- statement:
--   The Regime construction uses the x pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L82-L82
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L82-L82

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
variable {a : ℝ} {m : ℕ} (ha : 0 < a) (hm : (m : ℝ) ≤ (1 - d ^ (-(ε ^ 3))) * a)
include ha hm

theorem GJKKL.Main.Regime.x_pos {t : ℕ} (ht : t ≤ m) : 0 < pfrac a t := by sorry
