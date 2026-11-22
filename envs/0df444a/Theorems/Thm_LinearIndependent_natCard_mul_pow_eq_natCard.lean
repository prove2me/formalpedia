-- Prove2me | Theorems.Thm_LinearIndependent_natCard_mul_pow_eq_natCard
-- name    : LinearIndependent.natCard_mul_pow_eq_natCard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:04.627068+00:00
-- url     : https://prove2.me/theorems/eb555e60-e850-456b-bacf-f9043afa0247
-- title:
--   Linear Independent: nat Card mul pow eq nat Card
-- statement:
--   The linear maps vanishing at `r` linearly independent vectors form a proportion
--   `1 / Nat.card W ^ r` of all linear maps.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LinearMap/Card.lean#L61-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LinearMap/Card.lean#L61-L70

module
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LinearMap_Card
set_option autoImplicit true
@[expose] public section
public section
open Module
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {r : ℕ} {v : Fin r → V}

theorem LinearIndependent.natCard_mul_pow_eq_natCard (hv : LinearIndependent K v) :
    Nat.card {A : V →ₗ[K] W // ∀ i, A (v i) = 0} * Nat.card W ^ r = Nat.card (V →ₗ[K] W) := by sorry
