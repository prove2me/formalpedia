-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_g_le_simple
-- name    : GJKKL.Main.Regime.g_le_simple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:04.607682+00:00
-- url     : https://prove2.me/theorems/e6ff4490-53b0-47c2-bb30-a60a48321734
-- title:
--   Regime: g le simple
-- statement:
--   The one-step decrease of `dh` is at most `(k-1) d/a`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L99-L119
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L99-L119

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

theorem GJKKL.Main.Regime.g_le_simple {t : ℕ} (ht : t < m) :
    dhat k d a t - dhat k d a (t + 1) ≤ ((k : ℝ) - 1) * (d / a) := by sorry
