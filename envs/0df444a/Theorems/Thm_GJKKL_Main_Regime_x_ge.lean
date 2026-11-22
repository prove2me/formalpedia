-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_x_ge
-- name    : GJKKL.Main.Regime.x_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:18.589498+00:00
-- url     : https://prove2.me/theorems/775a8a64-7f24-4503-9be6-37d1701a17b2
-- title:
--   Regime: x ge
-- statement:
--   The Regime construction uses the x ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L80-L80
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L80-L80

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

theorem GJKKL.Main.Regime.x_ge {t : ℕ} (ht : t ≤ m) : d ^ (-(ε ^ 3)) ≤ pfrac a t := by sorry
