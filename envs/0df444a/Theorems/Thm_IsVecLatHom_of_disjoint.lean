-- Prove2me | Theorems.Thm_IsVecLatHom_of_disjoint
-- name    : IsVecLatHom.of_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:20.1578+00:00
-- url     : https://prove2.me/theorems/0a154c25-c5fa-42a4-b5cd-93369b2d7894
-- title:
--   Is Vec Lat Hom: of disjoint
-- statement:
--   A linear map that preserves disjointness is a vector lattice homomorphism.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L267-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L267-L284

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
open IsVecLatHom

theorem IsVecLatHom.of_disjoint {f : X → Y} (lin : IsLinearMap ℝ f)
    (disj : ∀ x y : X, x ⊓ y = 0 → f x ⊓ f y = 0) : IsVecLatHom f := by sorry
