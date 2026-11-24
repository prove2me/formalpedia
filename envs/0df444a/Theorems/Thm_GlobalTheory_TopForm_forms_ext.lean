-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_forms_ext
-- name    : GlobalTheory.TopForm.forms_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:42.304133+00:00
-- url     : https://prove2.me/theorems/80d8761c-26e9-432d-b0a5-7e339d51b4e5
-- title:
--   Top Form: forms ext
-- statement:
--   The Top Form construction uses the forms ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L217-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L217-L219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}

theorem GlobalTheory.TopForm.forms_ext {M : Type*} [AddCommGroup M] [Module B M] {ρ : A →+* B}
    {φ ψ : Forms α D →ₛₗ[ρ] M} (h : ∀ f, φ (dForm α f) = ψ (dForm α f)) : φ = ψ := by sorry
