-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_delta_nonneg
-- name    : GJKKL.Main.Regime.delta_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:35.82392+00:00
-- url     : https://prove2.me/theorems/032b9b9d-725a-4b03-88f8-979efc6283c6
-- title:
--   Regime: delta nonneg
-- statement:
--   The Regime construction uses the delta nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L95-L96
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L95-L96

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

theorem GJKKL.Main.Regime.delta_nonneg {t : ℕ} (ht : t ≤ m) : 0 ≤ delta k ε d a t := by sorry
