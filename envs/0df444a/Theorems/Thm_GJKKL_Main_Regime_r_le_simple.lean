-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_r_le_simple
-- name    : GJKKL.Main.Regime.r_le_simple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:22.236045+00:00
-- url     : https://prove2.me/theorems/56d814c5-ae94-4e64-b019-9b3200986809
-- title:
--   Regime: r le simple
-- statement:
--   The one-step growth of `δ` is at most `B d / (2a)`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L122-L162
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L122-L162

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

theorem GJKKL.Main.Regime.r_le_simple {t : ℕ} (ht : t < m) :
    delta k ε d a (t + 1) - delta k ε d a t ≤ (Bn k : ℝ) * (d / a) / 2 := by sorry
