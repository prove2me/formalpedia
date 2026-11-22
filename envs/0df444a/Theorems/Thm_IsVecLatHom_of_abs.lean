-- Prove2me | Theorems.Thm_IsVecLatHom_of_abs
-- name    : IsVecLatHom.of_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:20.9218+00:00
-- url     : https://prove2.me/theorems/1ec15bfb-3498-4ed6-80e5-6cb9693e05a7
-- title:
--   Is Vec Lat Hom: of abs
-- statement:
--   A linear map that preserves absolute values satisfies `IsVecLatHom`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L262-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L262-L264

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

theorem IsVecLatHom.of_abs {f : X → Y} (lin : IsLinearMap ℝ f) (abs : ∀ x : X, f |x|
  = |f x|) : IsVecLatHom f := by sorry
