-- Prove2me | Theorems.Thm_Lean4LPD_schur_mulVec_le
-- name    : Lean4LPD.schur_mulVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:24.831273+00:00
-- url     : https://prove2.me/theorems/4fb83a9a-a861-46fc-bc1a-6f066c91d4eb
-- title:
--   Lean4 LPD: schur mul Vec le
-- statement:
--   The same bound for `Matrix.mulVec`, without the bundled map `clm A`. The norm is the
--   Euclidean norm that Pauli coefficient vectors carry (`apd:thm:layer_inflow`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L103-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L103-L108

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
omit [DecidableEq κ]

theorem Lean4LPD.schur_mulVec_le (A : Matrix ι κ 𝕜) (y : EuclideanSpace 𝕜 κ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖toLp 2 (A *ᵥ y.ofLp)‖ ≤ Real.sqrt (R * C) * ‖y‖ := by sorry
