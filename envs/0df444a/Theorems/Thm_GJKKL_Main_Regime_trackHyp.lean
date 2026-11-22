-- Prove2me | Theorems.Thm_GJKKL_Main_Regime_trackHyp
-- name    : GJKKL.Main.Regime.trackHyp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:25.297255+00:00
-- url     : https://prove2.me/theorems/a7196bf1-b48c-40a3-8e81-4b4157e17297
-- title:
--   Regime: track Hyp
-- statement:
--   The Regime construction uses the track Hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L196-L418
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean#L196-L418

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
set_option maxHeartbeats 1600000

theorem GJKKL.Main.Regime.trackHyp (hunif : IsUniform H k)
    (hmin : ∀ v : V, (1 - d ^ (-ε)) * d ≤ (degree H v : ℝ))
    (hmax : ∀ v : V, (degree H v : ℝ) ≤ d)
    (hcod : ∀ u w : V, u ≠ w → (codegree H u w : ℝ) ≤ d ^ (1 - ε))
    (hn : ((k : ℝ) - 1) * d ^ ε / 2 ≤ Fintype.card V) {m : ℕ}
    (hm : (m : ℝ) ≤ (1 - d ^ (-(ε ^ 3))) * ((Fintype.card V : ℝ) / k)) :
    TrackHyp H k ⌊d ^ (1 - ε)⌋₊ (dhat k d ((Fintype.card V : ℝ) / k))
      (delta k ε d ((Fintype.card V : ℝ) / k)) m (Bn k : ℝ) (d ^ (1 - ε / 8) / 2)
      (100 * (k : ℝ) ^ 3 * d ^ (1 - ε)) (5 * k * d) := by sorry
