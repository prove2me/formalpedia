-- Prove2me | Theorems.Thm_Lean4LPD_schur_row_sq_le
-- name    : Lean4LPD.schur_row_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:37.36743+00:00
-- url     : https://prove2.me/theorems/14c98830-0b29-4f2b-8363-94e81b530b52
-- title:
--   Lean4 LPD: schur row sq le
-- statement:
--   Weighted Cauchy–Schwarz for one row: if row `i` of `A` has absolute sum at most `R`, then
--   `‖(A *ᵥ y) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2`. This is the row step of the Schur test used
--   in `apd:thm:layer_inflow`. Zero entries and empty sums need no separate case.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L45-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L45-L59

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
omit [Fintype ι]

theorem Lean4LPD.schur_row_sq_le (A : Matrix ι κ 𝕜) (y : κ → 𝕜) (i : ι) (R : ℝ)
    (hrow : ∑ j, ‖A i j‖ ≤ R) :
    ‖(A *ᵥ y) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 := by sorry
