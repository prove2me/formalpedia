-- Prove2me | Theorems.Thm_Lean4LPD_l2_opNorm_submatrix_le_one_of_mem_unitaryGroup
-- name    : Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_unitaryGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:37.598811+00:00
-- url     : https://prove2.me/theorems/c6d0e8af-7d31-4caa-ab53-8ce0dc1fec93
-- title:
--   Lean4 LPD: l2 op Norm submatrix le one of mem unitary Group
-- statement:
--   `Matrix.unitaryGroup` spelling.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean#L188-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean#L188-L192

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
omit [DecidableEq m] [DecidableEq p]

theorem Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ Matrix.unitaryGroup n 𝕜) {f : p → n} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖U.submatrix f g‖ ≤ 1 := by sorry
