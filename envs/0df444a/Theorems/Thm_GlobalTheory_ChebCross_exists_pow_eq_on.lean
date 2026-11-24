-- Prove2me | Theorems.Thm_GlobalTheory_ChebCross_exists_pow_eq_on
-- name    : GlobalTheory.ChebCross.exists_pow_eq_on
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:13.482947+00:00
-- url     : https://prove2.me/theorems/bc4aed71-133b-4e62-ac74-d20fb2b5c07d
-- title:
--   Cheb Cross: exists pow eq on
-- statement:
--   The Cheb Cross construction uses the exists pow eq on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L71-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCyclotomicCrossingFieldDecidingFrobenius.lean#L71-L99

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

theorem GlobalTheory.ChebCross.exists_pow_eq_on (M : IntermediateField F Ω) [FiniteDimensional F M] [IsGalois F M]
    (h σ : Ω ≃ₐ[F] Ω)
    (hσ : σ ∈ (M ⊓ IntermediateField.fixedField (Subgroup.zpowers h)).fixingSubgroup) :
    ∃ k : ℕ, ∀ x ∈ M, σ x = (h ^ k) x := by sorry
