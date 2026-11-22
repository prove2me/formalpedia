-- Prove2me | Theorems.Thm_IsVLArchimedean_eq_zero_of_nonneg_of_forall_nsmul_le
-- name    : IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:51.479409+00:00
-- url     : https://prove2.me/theorems/6e554c37-522c-4749-9b28-9006950b5ad1
-- title:
--   Is VLArchimedean: eq zero of nonneg of forall nsmul le
-- statement:
--   Non-negative form of the Archimedean property.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L430-L432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Basic.lean#L430-L432

module
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (x y : X)
open IsVLArchimedean
omit [VectorLattice X]

theorem IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le [IsVLArchimedean X] {x y : X}
    (hx : 0 ≤ x) (h : ∀ n : ℕ, n • x ≤ y) : x = 0 := by sorry
