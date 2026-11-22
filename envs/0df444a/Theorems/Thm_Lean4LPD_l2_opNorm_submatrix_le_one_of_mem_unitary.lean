-- Prove2me | Theorems.Thm_Lean4LPD_l2_opNorm_submatrix_le_one_of_mem_unitary
-- name    : Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_unitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:54.165321+00:00
-- url     : https://prove2.me/theorems/3021c0de-9783-4a19-bae8-0108192941cd
-- title:
--   Lean4 LPD: l2 op Norm submatrix le one of mem unitary
-- statement:
--   **A block of a unitary matrix has ℓ² operator norm at most `1`.**
--
--   `f` and `g` are injective index maps, e.g. `Subtype.val` out of the two index subtypes cutting the
--   block out. No nonemptiness hypothesis on any of `n`, `p`, `q`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean#L180-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/BlockNorm.lean#L180-L184

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

theorem Lean4LPD.l2_opNorm_submatrix_le_one_of_mem_unitary {U : Matrix n n 𝕜}
    (hU : U ∈ unitary (Matrix n n 𝕜)) {f : p → n} {g : q → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖U.submatrix f g‖ ≤ 1 := by sorry
