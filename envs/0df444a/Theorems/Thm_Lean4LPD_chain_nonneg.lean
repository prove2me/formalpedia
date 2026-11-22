-- Prove2me | Theorems.Thm_Lean4LPD_chain_nonneg
-- name    : Lean4LPD.chain_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:11.200501+00:00
-- url     : https://prove2.me/theorems/eb9f844e-f29c-4006-90f4-85bddbadccfd
-- title:
--   Lean4 LPD: chain nonneg
-- statement:
--   The Lean4 LPD construction uses the chain nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L119-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L119-L130

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

theorem Lean4LPD.chain_nonneg (heps : ∀ j m, 0 ≤ eps j m) (hE : ∀ m, 0 ≤ E m) :
    ∀ k m : ℕ, 0 ≤ chain eps E k m := by sorry
