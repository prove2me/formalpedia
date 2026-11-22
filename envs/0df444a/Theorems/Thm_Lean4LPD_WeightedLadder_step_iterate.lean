-- Prove2me | Theorems.Thm_Lean4LPD_WeightedLadder_step_iterate
-- name    : Lean4LPD.WeightedLadder.step_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:16.080795+00:00
-- url     : https://prove2.me/theorems/409d9c53-ac49-4696-8630-031f534f83ee
-- title:
--   Weighted Ladder: step iterate
-- statement:
--   Iterating the flow recursion over the `g` layers, using `N m 0 = 0` for `m ≥ 1` to kill the
--   boundary term. The rung-dependent analogue of `Lean4LPD.Ladder.step_iterate`; like it, this needs
--   no sign hypothesis on `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L94-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L94-L104

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

theorem Lean4LPD.WeightedLadder.step_iterate {m : ℕ} (hm : 1 ≤ m) :
    ∀ g : ℕ, L.N m g ≤ c m * ∑ l ∈ range g, L.N (m - 1) l := by sorry
