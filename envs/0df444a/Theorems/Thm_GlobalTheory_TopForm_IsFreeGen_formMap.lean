-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_IsFreeGen_formMap
-- name    : GlobalTheory.TopForm.IsFreeGen.formMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:47.482416+00:00
-- url     : https://prove2.me/theorems/b683433b-0bb5-4bf4-94f2-6f16a5d7f51c
-- title:
--   Is Free Gen: form Map
-- statement:
--   The Is Free Gen construction uses the form Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L236-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L236-L244

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

theorem GlobalTheory.TopForm.IsFreeGen.formMap {ρ : A →+* B} (hρ : ρ.Etale) (h : ρ.comp α = β) {ω : Forms α D}
    (hω : IsFreeGen A ω) : IsFreeGen B (formMap D ρ h ω) := by sorry
