-- Prove2me | Theorems.Thm_Lean4LPD_l2_opNorm_submatrix_le_one_of_mem_orthogonalGroup
-- name    : Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_orthogonalGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:36.86471+00:00
-- url     : https://prove2.me/theorems/fb80a212-9ea5-4fc3-a909-217eb46bc388
-- title:
--   Lean4 LPD: l2 op Norm submatrix le one of mem orthogonal Group
-- statement:
--   **Real orthogonal case**, the `𝕜 = ℝ` specialization: a block of an orthogonal matrix has ℓ²
--   operator norm at most `1`.  `Matrix.orthogonalGroup n ℝ` is by definition `unitary (Matrix n n ℝ)`
--   with the trivial star, so this is literally the unitary statement at `𝕜 = ℝ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean#L205-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean#L205-L209

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

theorem Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_orthogonalGroup {O : Matrix n n ℝ}
    (hO : O ∈ Matrix.orthogonalGroup n ℝ) {f : p → n} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖O.submatrix f g‖ ≤ 1 := by sorry
