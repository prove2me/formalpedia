-- Prove2me | Theorems.Thm_Lean4LPD_l2_opNorm_le_of_row_col_bound
-- name    : Lean4LPD.l2_opNorm_le_of_row_col_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:37.87807+00:00
-- url     : https://prove2.me/theorems/8432bf21-3af2-438a-8580-118b8910dd40
-- title:
--   Lean4 LPD: l2 op Norm le of row col bound
-- statement:
--   If `B` bounds every row sum and every column sum, then `‖A‖ ≤ B`: the case `R = C = B` of
--   `l2_opNorm_le_schur`. This is the form `Pauli/LayerFlow` applies to the layer inflow matrices
--   (`apd:thm:layer_inflow`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L123-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L123-L127

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset Matrix WithLp
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq κ]

theorem Lean4LPD.l2_opNorm_le_of_row_col_bound (A : Matrix ι κ 𝕜) {B : ℝ}
    (hB : 0 ≤ B) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ B)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ B) : ‖A‖ ≤ B := by sorry
