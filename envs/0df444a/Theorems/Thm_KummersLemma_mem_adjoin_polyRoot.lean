-- Prove2me | Theorems.Thm_KummersLemma_mem_adjoin_polyRoot
-- name    : KummersLemma.mem_adjoin_polyRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:00.219588+00:00
-- url     : https://prove2.me/theorems/5f67ecea-7446-4f8a-8906-7456d71b4737
-- title:
--   Kummers Lemma: mem adjoin poly Root
-- statement:
--   The Kummers Lemma construction uses the mem adjoin poly Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/Field.lean#L286-L293
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/Field.lean#L286-L293

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

theorem KummersLemma.mem_adjoin_polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    α ∈ Algebra.adjoin K {(polyRoot hp hζ u hcong α e i : L)} := by sorry
