-- Prove2me | Theorems.Thm_Ideal_isPrincipal_pow_finrank_of_isPrincipal_map
-- name    : Ideal.isPrincipal_pow_finrank_of_isPrincipal_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:51.823161+00:00
-- url     : https://prove2.me/theorems/09e6f5f4-6cb4-489f-b808-fb8b108612a0
-- title:
--   Ideal: is Principal pow finrank of is Principal map
-- statement:
--   The Ideal construction uses the is Principal pow finrank of is Principal map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L82-L92

module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Theorems.Thm_Hilbert92

set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField
variable {K : Type} [Field K]
open Polynomial Module
variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]
variable [IsGalois K L]

theorem Ideal.isPrincipal_pow_finrank_of_isPrincipal_map [IsDedekindDomain A] {I : Ideal A}
    (hI : (I.map (algebraMap A B)).IsPrincipal) : (I ^ finrank K L).IsPrincipal := by sorry
