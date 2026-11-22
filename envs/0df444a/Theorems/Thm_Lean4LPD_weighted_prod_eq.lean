-- Prove2me | Theorems.Thm_Lean4LPD_weighted_prod_eq
-- name    : Lean4LPD.weighted_prod_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:13.862883+00:00
-- url     : https://prove2.me/theorems/d0832eb9-b4b6-47bd-8340-7d38b36c8399
-- title:
--   Lean4 LPD: weighted prod eq
-- statement:
--   The product reindexing relating the two ways of writing part (ii) of
--   `apd:cor:norm_cumulation_jump`: `∏_{j=1}^{m} (w_{j+1} · a) = a^m · ∏_{j=2}^{m+1} w_j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L142-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Weighted.lean#L142-L153

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

theorem Lean4LPD.weighted_prod_eq (w : ℕ → ℝ) (a : ℝ) :
    ∀ m : ℕ, (∏ j ∈ Finset.Icc 1 m, w (j + 1) * a) = a ^ m * ∏ j ∈ Finset.Icc 2 (m + 1), w j := by sorry
