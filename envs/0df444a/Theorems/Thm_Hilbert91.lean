-- Prove2me | Theorems.Thm_Hilbert91
-- name    : Hilbert91
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:26.632399+00:00
-- url     : https://prove2.me/theorems/aa563d44-c05f-4a8b-a7e9-06b2f35f6815
-- title:
--   Hilbert91: Hilbert91
-- statement:
--   The Hilbert91 construction uses the Hilbert91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L594-L596
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L594-L596

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
variable [IsGalois k K]
attribute [local instance] _p2m_local_instance_fee6646a52_507
attribute [local instance] _p2m_local_instance_fee6646a52_512
attribute [local instance] _p2m_local_instance_fee6646a52_515
variable [IsUnramifiedAtInfinitePlaces k K]

theorem Hilbert91 : ∃ S : systemOfUnits p G (NumberField.Units.rank k + 1), S.IsFundamental := by sorry
