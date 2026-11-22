-- Prove2me | Theorems.Thm_Lean4LPD_schur_clm_le
-- name    : Lean4LPD.schur_clm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:45.26855+00:00
-- url     : https://prove2.me/theorems/15d3b9a6-1c52-4769-a90d-858eabd9aaf3
-- title:
--   Lean4 LPD: schur clm le
-- statement:
--   The Schur test as a bound on the action of `clm A`, the continuous linear map of Euclidean
--   spaces attached to `A` in `BlockNorm`: `‖clm A y‖ ≤ √(R * C) * ‖y‖` (`apd:thm:layer_inflow`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L88-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L88-L98

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

theorem Lean4LPD.schur_clm_le (A : Matrix ι κ 𝕜) (y : EuclideanSpace 𝕜 κ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖clm A y‖ ≤ Real.sqrt (R * C) * ‖y‖ := by sorry
