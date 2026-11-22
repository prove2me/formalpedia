-- Prove2me | Theorems.Thm_Lean4LPD_WeightedLadder_cumulation
-- name    : Lean4LPD.WeightedLadder.cumulation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:13.872597+00:00
-- url     : https://prove2.me/theorems/2f921e9a-faba-4337-815c-9ad635490dec
-- title:
--   Weighted Ladder: cumulation
-- statement:
--   **Cumulation with a rung-dependent damping factor.**
--
--     `N_{≥m}^{(g)} ≤ C(g, m) · (∏_{j=1}^{m} c j) · M`.
--
--   The same induction as `Lean4LPD.Ladder.cumulation`: iterate the recursion over `g`, insert the
--   inductive hypothesis, and close with the hockey-stick identity. Only `0 ≤ c j` is needed, never
--   `c j ≤ 1`, even though the intended `c j = w_{j+1} sin(dt)` need not be below one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L113-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L113-L136

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.WeightedLadder
variable {c : ℕ → ℝ} {M : ℝ} (L : WeightedLadder c M)

theorem Lean4LPD.WeightedLadder.cumulation (hc : ∀ j, 0 ≤ c j) :
    ∀ m g : ℕ, L.N m g ≤ (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M := by sorry
