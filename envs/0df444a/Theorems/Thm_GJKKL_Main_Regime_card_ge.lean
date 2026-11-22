-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_card_ge
-- name    : GJKKL.Main.Regime.card_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:03.936171+00:00
-- url     : https://prove2.me/theorems/dcf62ac2-115e-48a3-8c6e-cfa79c1420fa
-- title:
--   Regime: card ge
-- statement:
--   Many vertices: `n ≥ (k-1) d^ε / 2`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L39-L71
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L39-L71

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

theorem GJKKL.Main.Regime.card_ge (hunif : IsUniform H k)
    (hmin : ∀ v : V, (1 - d ^ (-ε)) * d ≤ (degree H v : ℝ))
    (hcod : ∀ u w : V, u ≠ w → (codegree H u w : ℝ) ≤ d ^ (1 - ε)) (v : V) :
    ((k : ℝ) - 1) * d ^ ε / 2 ≤ Fintype.card V := by sorry
