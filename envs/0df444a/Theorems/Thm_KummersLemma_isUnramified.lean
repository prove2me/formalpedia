-- Prove2me | Theorems.Thm_KummersLemma_isUnramified
-- name    : KummersLemma.isUnramified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:56.358796+00:00
-- url     : https://prove2.me/theorems/300630df-ccbe-430a-9b4d-ddccba553dfa
-- title:
--   Kummers Lemma: is Unramified
-- statement:
--   The Kummers Lemma construction uses the is Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/Field.lean#L297-L318
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/Field.lean#L297-L318

module
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
variable (u : (𝓞 K)ˣ)
  (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ p ≠ u)
open Polynomial IsCyclotomicExtension.Rat
open KummersLemma
variable [IsCyclotomicExtension {p} ℚ K]
include hu hp hζ hcong
attribute [local instance] Ideal.Quotient.field

theorem KummersLemma.isUnramified (L) [Field L] [Algebra K L] [IsSplittingField K L (X ^ p - C (u : K))] :
    Algebra.Unramified (𝓞 K) (𝓞 L) := by sorry
