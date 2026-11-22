-- Prove2me | Theorems.Thm_Lean4LPD_schur_mulVec_sq_le
-- name    : Lean4LPD.schur_mulVec_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:34.888145+00:00
-- url     : https://prove2.me/theorems/f779ef9b-c08b-4818-abf1-b8f46ee5ba90
-- title:
--   Lean4 LPD: schur mul Vec sq le
-- statement:
--   Squared form of the finite Schur test used in `apd:thm:layer_inflow`: if every row of `A`
--   has absolute sum at most `R` and every column at most `C`, then
--   `∑ i, ‖(A *ᵥ y) i‖ ^ 2 ≤ R * C * ∑ j, ‖y j‖ ^ 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L64-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L64-L82

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

theorem Lean4LPD.schur_mulVec_sq_le (A : Matrix ι κ 𝕜) (y : κ → 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    (∑ i, ‖(A *ᵥ y) i‖ ^ 2) ≤ R * C * ∑ j, ‖y j‖ ^ 2 := by sorry
