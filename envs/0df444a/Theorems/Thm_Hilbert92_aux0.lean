-- Prove2me | Theorems.Thm_Hilbert92_aux0
-- name    : Hilbert92_aux0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:23.563625+00:00
-- url     : https://prove2.me/theorems/53723606-5e6d-4121-a5f4-5558023284f0
-- title:
--   Hilbert92 aux0: Hilbert92 aux0
-- statement:
--   The Hilbert92 aux0 construction uses the Hilbert92 aux0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L192-L205
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L192-L205

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
include hKL

theorem Hilbert92_aux0 (h : ℕ) (ν : (𝓞 k)ˣ) (hν : IsPrimitiveRoot (ν : k) (p ^ h))
    (H : ∀ ε : (𝓞 K)ˣ, algebraMap k K ν ^ (p ^ (h - 1)) ≠ ε / (σ ε : K)) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by sorry
