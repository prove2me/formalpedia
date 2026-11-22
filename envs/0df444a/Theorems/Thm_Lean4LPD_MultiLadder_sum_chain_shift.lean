-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_sum_chain_shift
-- name    : Lean4LPD.MultiLadder.sum_chain_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:51.067885+00:00
-- url     : https://prove2.me/theorems/efd9dee0-821c-4d7d-9469-3b0644092dcf
-- title:
--   Multi Ladder: sum chain shift
-- statement:
--   The shifted chain sum, unrolled one level: the `k = 0` term is the entry factor `E m`, and
--   every remaining term ends with a `j`-jump that starts from rung `m - j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L251-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L251-L274

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
open Lean4LPD.MultiLadder
variable {M : ℝ}
variable {eps : ℕ → ℕ → ℝ} {E : ℕ → ℝ}

theorem Lean4LPD.MultiLadder.sum_chain_shift (m T : ℕ) :
    ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m
      = E m + ∑ j ∈ Ico 1 m, eps j m
          * ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k (m - j) := by sorry
