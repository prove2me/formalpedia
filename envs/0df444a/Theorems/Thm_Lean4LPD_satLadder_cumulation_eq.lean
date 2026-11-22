-- Prove2me | Theorems.Thm_Lean4LPD_satLadder_cumulation_eq
-- name    : Lean4LPD.satLadder_cumulation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:06:31.423173+00:00
-- url     : https://prove2.me/theorems/d2320362-abec-454d-8085-eca6add658c9
-- title:
--   Lean4 LPD: sat Ladder cumulation eq
-- statement:
--   The bound of `cumulation` is **attained**: at the saturating family it is an equality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L212-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L212-L213

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

theorem Lean4LPD.satLadder_cumulation_eq {c : ℕ → ℝ} {M : ℝ} (hc : ∀ j, 0 ≤ c j) (hM : 0 ≤ M) (m g : ℕ) :
    (satLadder hc hM).N m g = (g.choose m : ℝ) * (∏ j ∈ Icc 1 m, c j) * M := by sorry
