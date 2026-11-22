-- Prove2me | Theorems.Thm_Lean4LPD_chain_diag
-- name    : Lean4LPD.chain_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:04:43.979979+00:00
-- url     : https://prove2.me/theorems/a1a8745d-df2f-44d6-89ae-d4015811b326
-- title:
--   Lean4 LPD: chain diag
-- statement:
--   **The all-ones term is the single-jump layer-cumulation bound.** Formalizes the statement
--   of `apd:rmk:multijump` that the term of the majorant with `k = m` jumps, all of length one (so
--   `ν_i = i`), coincides with the bound `apd:eq:layer_cumulation`:
--
--     `chain ε E m m = E 1 · ∏_{i=2}^{m} ε_1^{(i)}`.
--
--   A composition of `m` into `m` parts has every part equal to one: in the defining recursion a
--   last jump of length `j ≥ 2` would leave `m - 1` jumps to reach rung `m - j < m - 1`, and that
--   term vanishes by `chain_eq_zero_of_lt`. With `ε_1^{(i)} = w_{i+1} sin(dt)` this product is
--   `sin^{m-1}(dt) ∏_{j=3}^{m+1} w_j`, which is `Lean4LPD.layer_cumulation`'s product with the entry
--   rung's factor replaced by `E 1` — the one place the two bounds differ, and the reason the entry
--   factor is kept separate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L161-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/MultiJump.lean#L161-L187

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

theorem Lean4LPD.chain_diag :
    ∀ m : ℕ, 1 ≤ m → chain eps E m m = E 1 * ∏ i ∈ Ico 2 (m + 1), eps 1 i := by sorry
