-- Prove2me | Theorems.Thm_Hilbert92_aux1
-- name    : Hilbert92_aux1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:09.340284+00:00
-- url     : https://prove2.me/theorems/8b1e8339-be05-4deb-84db-416e88164cba
-- title:
--   Hilbert92 aux1: Hilbert92 aux1
-- statement:
--   The Hilbert92 aux1 construction uses the Hilbert92 aux1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L470-L487
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L470-L487

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
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
variable [NumberField K]
include hKL

theorem Hilbert92_aux1 (n : ℕ) (H : Fin n → Additive (𝓞 K)ˣ) (ν : (𝓞 k)ˣ)
    (a : ℤ) (ι : Fin n → ℤ) (η : Fin n → Additive (𝓞 k)ˣ)
    (ha : ∑ i : Fin n, ι i • η i = (a * ↑↑p) • Additive.ofMul ν)
    (hη :
      ∀ i, Additive.toMul (η i) = Algebra.norm k (S := K) ((Additive.toMul (H i) : _) : K)) :
    letI J : (𝓞 K)ˣ := (Additive.toMul (∑ i : Fin n, ι i • H i)) *
      (Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ν) ^ (-a)
    Algebra.norm k (S := K) ((J : (𝓞 K)ˣ) : K) = 1 := by sorry
