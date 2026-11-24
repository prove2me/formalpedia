-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_formMap_formMap
-- name    : GlobalTheory.TopForm.formMap_formMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:32.999816+00:00
-- url     : https://prove2.me/theorems/803fbeed-7e49-4236-a0a8-668a9290f761
-- title:
--   Top Form: form Map form Map
-- statement:
--   The Top Form construction uses the form Map form Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L221-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L221-L228

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

theorem GlobalTheory.TopForm.formMap_formMap (ρ : A →+* B) (σ : B →+* C) (τ : A →+* C) (e : σ.comp ρ = τ)
    (h : ρ.comp α = β) (h' : σ.comp β = γ) (h'' : τ.comp α = γ) (x : Forms α D) :
    formMap D σ h' (formMap D ρ h x) = formMap D τ h'' x := by sorry
