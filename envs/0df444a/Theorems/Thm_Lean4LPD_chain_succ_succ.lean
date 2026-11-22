-- Prove2me | Theorems.Thm_Lean4LPD_chain_succ_succ
-- name    : Lean4LPD.chain_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:09.254814+00:00
-- url     : https://prove2.me/theorems/2599bec7-9aad-4cb9-8662-d9a2b61a6242
-- title:
--   Lean4 LPD: chain succ succ
-- statement:
--   The Lean4 LPD construction uses the chain succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L114-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L114-L115

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

theorem Lean4LPD.chain_succ_succ (eps : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (k m : ℕ) :
    chain eps E (k + 2) m = ∑ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j) := by sorry
