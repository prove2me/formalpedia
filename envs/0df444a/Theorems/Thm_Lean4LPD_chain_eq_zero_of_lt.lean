-- Prove2me | Theorems.Thm_Lean4LPD_chain_eq_zero_of_lt
-- name    : Lean4LPD.chain_eq_zero_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:04.346535+00:00
-- url     : https://prove2.me/theorems/74276752-ed39-4eb3-a49f-d2b5751cf8ec
-- title:
--   Lean4 LPD: chain eq zero of lt
-- statement:
--   A path to rung `m ≥ 1` cannot use more than `m` jumps, each jump climbing at least one rung.
--   This is what makes the outer sum of `apd:eq:composition_majorant` run to `min(m, T)` even though
--   `majorant` below sums to `T`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L135-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L135-L147

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}

theorem Lean4LPD.chain_eq_zero_of_lt : ∀ k m : ℕ, 1 ≤ m → m < k → chain eps E k m = 0 := by sorry
