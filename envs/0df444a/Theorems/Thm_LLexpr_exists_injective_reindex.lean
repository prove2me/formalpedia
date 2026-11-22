-- Prove2me | Theorems.Thm_LLexpr_exists_injective_reindex
-- name    : LLexpr.exists_injective_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:20.817161+00:00
-- url     : https://prove2.me/theorems/eca5aa0e-9a98-4958-ba69-d2fca681b749
-- title:
--   LLexpr: exists injective reindex
-- statement:
--   Any finite family factors through an injective finite family listing its range.
--
--   The map `f` records, for each original index, the corresponding index in the
--   range listing. This is useful when reducing an arbitrary finite tuple to a
--   tuple of distinct entries.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L104-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L104-L116

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem LLexpr.exists_injective_reindex {ι : Type*} {n : ℕ} (a : Fin n → ι) :
    ∃ (m : ℕ) (b : Fin m → ι) (_ : Function.Injective b) (f : Fin n → Fin m),
      ∀ i, b (f i) = a i := by sorry
