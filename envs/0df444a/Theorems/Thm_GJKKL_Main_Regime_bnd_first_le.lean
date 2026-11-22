-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_bnd_first_le
-- name    : GJKKL.Main.Regime.bnd_first_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:14.084385+00:00
-- url     : https://prove2.me/theorems/b2939fe2-a9a8-4bc0-8fd5-2de6c7b128d1
-- title:
--   Regime: bnd first le
-- statement:
--   The per-step variation bound.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L165-L189
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L165-L189

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

theorem GJKKL.Main.Regime.bnd_first_le {t : ℕ} (ht : t < m) :
    ((k : ℝ) - 1) * (dhat k d a t + delta k ε d a t) ^ 2 /
        (a * pfrac a t * (dhat k d a t - delta k ε d a t)) ≤ 9 / 2 * ((k : ℝ) - 1) * (d / a) := by sorry
