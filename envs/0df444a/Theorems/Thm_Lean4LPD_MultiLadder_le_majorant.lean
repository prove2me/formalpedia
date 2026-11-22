-- Prove2me | Theorems.Thm_Lean4LPD_MultiLadder_le_majorant
-- name    : Lean4LPD.MultiLadder.le_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:11.162513+00:00
-- url     : https://prove2.me/theorems/5743627a-9da9-46c9-83f5-709413a3499a
-- title:
--   Multi Ladder: le majorant
-- statement:
--   **The first-passage majorant.** Formalizes `apd:eq:composition_majorant`:
--
--     `N_m^{(T)} ≤ ‖O‖ · ∑_{k} C(T,k) · chain_k^{(m)}`,
--     `chain_k^{(m)} = ∑_{0<ν₁<⋯<ν_k=m} E_{ν₁} ∏_{i=2}^{k} ε_{ν_i-ν_{i-1}}^{(ν_i)}`.
--
--   The inner chain sum is `chain`, defined by peeling the last jump. Only nonnegativity of `eps` is
--   needed; `E` and `M` are unconstrained, so the bound is inherited by any `E` majorizing the
--   overshoot tail.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L284-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L284-L319

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

theorem Lean4LPD.MultiLadder.le_majorant (L : MultiLadder eps E M) (heps : ∀ j m, 0 ≤ eps j m) :
    ∀ T : ℕ, ∀ m : ℕ, 1 ≤ m → L.N m T ≤ majorant eps E M m T := by sorry
