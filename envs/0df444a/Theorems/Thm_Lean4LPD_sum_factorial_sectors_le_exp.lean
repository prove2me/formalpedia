-- Prove2me | Theorems.Thm_Lean4LPD_sum_factorial_sectors_le_exp
-- name    : Lean4LPD.sum_factorial_sectors_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:02.713834+00:00
-- url     : https://prove2.me/theorems/bf228d57-768e-4d42-8587-a7071bc2af98
-- title:
--   Lean4 LPD: sum factorial sectors le exp
-- statement:
--   The factorial and composition-count factors in `apd:eq:total_high_weight_norm` are bounded
--   by the exponential series, for every `m` at once:
--   `∑_{D<m} C(m-1, D) · m!/(m-D)! · y^D ≤ exp(m² y)` for `y ≥ 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L176-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/AssemblyBound.lean#L176-L193

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.sum_factorial_sectors_le_exp (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (∑ D ∈ range m, ((m - 1).choose D : ℝ) *
      ((Nat.factorial m : ℝ) / (Nat.factorial (m - D) : ℝ)) * y ^ D) ≤
      Real.exp ((m : ℝ) ^ 2 * y) := by sorry
