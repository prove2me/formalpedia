-- Prove2me | Theorems.Thm_GlobalTheory_ChebCross_cross
-- name    : GlobalTheory.ChebCross.cross
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:20.839403+00:00
-- url     : https://prove2.me/theorems/81adaefa-dfe9-4c5b-b3cc-ea252ff9ebeb
-- title:
--   Cheb Cross: cross
-- statement:
--   The Cheb Cross construction uses the cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L101-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L101-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicCrossingFieldDecidingFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.ChebCross
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem GlobalTheory.ChebCross.cross : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : G F Ω) (m : ℕ), m.Prime → Module.finrank F L ∣ m - 1 → Irreducible (cyclotomic m L) → ∃ (Z : IntermediateField F Ω) (τ : (ZMod m)ˣ), FiniteDimensional F Z ∧ Irreducible (cyclotomic m Z) ∧ ∀ σ : G F Ω, σ ∈ Z.fixingSubgroup → (∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ (τ : ZMod m).val) → σ * g⁻¹ ∈ L.fixingSubgroup := by sorry
