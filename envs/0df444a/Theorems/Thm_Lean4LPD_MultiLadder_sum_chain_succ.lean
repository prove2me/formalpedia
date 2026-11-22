-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_sum_chain_succ
-- name    : Lean4LPD.MultiLadder.sum_chain_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:01:25.69543+00:00
-- url     : https://prove2.me/theorems/89c44e7a-9405-4638-91d6-c6535c2104d5
-- title:
--   Multi Ladder: sum chain succ
-- statement:
--   The Pascal recursion satisfied by the majorant's bracket, which is the whole content of the
--   induction behind `apd:eq:composition_majorant`. Among the paths with `k` jumps in `T` layers,
--   those whose final layer is idle are counted by `C(T-1,k)` and those that jump in the final layer
--   by `C(T-1,k-1)`; the two cases add up by Pascal's rule.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L224-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L224-L247

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

theorem Lean4LPD.MultiLadder.sum_chain_succ (m T : ℕ) :
    ∑ k ∈ range (T + 2), ((T + 1).choose k : ℝ) * chain eps E k m
      = (∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E k m)
        + ∑ k ∈ range (T + 1), (T.choose k : ℝ) * chain eps E (k + 1) m := by sorry
