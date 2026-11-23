-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
-- name    : GlobalTheory.TopForm.formMap_dForm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:18.872526+00:00
-- url     : https://prove2.me/theorems/bb5a6686-acd7-40dd-8f51-c7fc73d5e93a
-- title:
--   Top Form: form Map d Form
-- statement:
--   The Top Form construction uses the form Map d Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L206-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L206-L215

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

theorem GlobalTheory.TopForm.formMap_dForm (ρ : A →+* B) (h : ρ.comp α = β) (f : Fin D → A) :
    formMap D ρ h (dForm α f) = dForm β fun i => ρ (f i) := by sorry
