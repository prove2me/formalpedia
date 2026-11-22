-- Prove2me | Theorems.Thm_GJKKL_lossSum_ge_real
-- name    : GJKKL.lossSum_ge_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:04.476819+00:00
-- url     : https://prove2.me/theorems/4fd4843e-0a79-4344-a134-83bf30dc6ab6
-- title:
--   GJKKL: loss Sum ge real
-- statement:
--   The GJKKL construction uses the loss Sum ge real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L87-L106
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L87-L106

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.lossSum_ge_real (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    {dh δ : ℕ → ℝ} {h : List (Finset V)} (ht : Tracked H dh δ h) (v : V) {c : ℕ}
    (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    (dv H h v : ℝ) * ((k : ℝ) - 1) * (dh h.length - δ h.length) -
        (dv H h v : ℝ) * ((((k - 1) + (k - 1) * (k - 2) : ℕ) : ℝ)) * c ≤ lossSum H h v := by sorry
