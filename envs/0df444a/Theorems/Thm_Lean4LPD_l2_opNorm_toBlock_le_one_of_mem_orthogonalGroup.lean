-- Prove2me | Theorems.Thm_Lean4LPD_l2_opNorm_toBlock_le_one_of_mem_orthogonalGroup
-- name    : Lean4LPD.l2_opNorm_toBlock_le_one_of_mem_orthogonalGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:42.808941+00:00
-- url     : https://prove2.me/theorems/44239587-f250-4457-9097-8e2d7d9cb8e5
-- title:
--   Lean4 LPD: l2 op Norm to Block le one of mem orthogonal Group
-- statement:
--   `Matrix.toBlock` form of the orthogonal case.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean#L213-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean#L213-L216

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_SchurCore
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_BlockNorm
set_option autoImplicit true
@[expose] public section
open scoped Matrix.Norms.L2Operator
open Matrix Finset WithLp
public section
open Lean4LPD
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
omit [DecidableEq m]

theorem Lean4LPD.l2_opNorm_toBlock_le_one_of_mem_orthogonalGroup {O : Matrix n n ℝ}
    (hO : O ∈ Matrix.orthogonalGroup n ℝ) (P Q : n → Prop) [DecidablePred P] [DecidablePred Q] :
    ‖O.toBlock P Q‖ ≤ 1 := by sorry
