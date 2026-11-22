-- Prove2me | Theorems.Thm_LLexpr_map_eval
-- name    : LLexpr.map_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:17.57232+00:00
-- url     : https://prove2.me/theorems/ce311d79-ddf0-42b2-bb3f-afe8cfcb7bbd
-- title:
--   LLexpr: map eval
-- statement:
--   A vector lattice homomorphism commutes with evaluation of lattice-linear expressions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L235-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L235-L246

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]
open LLexpr
variable {n : ℕ}

theorem LLexpr.map_eval {Y Z : Type*}
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (T : VecLatHom Y Z) (y : Fin n → Y) (e : LLexpr n) :
    T (eval y e) = eval (fun i => T (y i)) e := by sorry
