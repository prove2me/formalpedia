-- Prove2me | Theorems.Thm_GlobalTheory_ChebCross_irreducible_of_onto
-- name    : GlobalTheory.ChebCross.irreducible_of_onto
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:15.627824+00:00
-- url     : https://prove2.me/theorems/02e57706-19a8-4811-8d63-0678c7d0b49f
-- title:
--   Cheb Cross: irreducible of onto
-- statement:
--   The Cheb Cross construction uses the irreducible of onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L39-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L39-L69

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

theorem GlobalTheory.ChebCross.irreducible_of_onto [CharZero Ω] (Z : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m)
    (h : ∀ j : (ZMod m)ˣ, ∃ u : Ω ≃ₐ[F] Ω, u ∈ Z.fixingSubgroup ∧ hζ.autToPow F u = j) :
    Irreducible (cyclotomic m Z) := by sorry
