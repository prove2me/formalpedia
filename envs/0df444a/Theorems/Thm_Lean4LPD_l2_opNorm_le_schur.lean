-- Prove2me | Theorems.Thm_Lean4LPD_l2_opNorm_le_schur
-- name    : Lean4LPD.l2_opNorm_le_schur
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:00:31.875777+00:00
-- url     : https://prove2.me/theorems/afe5516a-3658-422c-9ec7-72051d02dd79
-- title:
--   Lean4 LPD: l2 op Norm le schur
-- statement:
--   **The finite Schur test**, in the form used by `apd:thm:layer_inflow`: row sums at most `R`
--   and column sums at most `C` give `‖A‖ ≤ √(R * C)`. Here `‖A‖` is the scoped **ℓ² operator norm**
--   (`Matrix.Norms.L2Operator`), not an entrywise matrix norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L113-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/SchurCore.lean#L113-L118

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

theorem Lean4LPD.l2_opNorm_le_schur (A : Matrix ι κ 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) : ‖A‖ ≤ Real.sqrt (R * C) := by sorry
