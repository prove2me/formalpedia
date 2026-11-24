-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_map_dForm_mul_sub_mem
-- name    : GlobalTheory.TopForm.map_dForm_mul_sub_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:32.241176+00:00
-- url     : https://prove2.me/theorems/18dde639-3c7a-46ed-b2b9-ff8f75eae927
-- title:
--   Top Form: map d Form mul sub mem
-- statement:
--   The Top Form construction uses the map d Form mul sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L267-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L267-L273

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

theorem GlobalTheory.TopForm.map_dForm_mul_sub_mem (c : Forms α D →ₗ[A] A) (I : Ideal A) (h : A) (g : Fin D → A)
    (hg : ∀ i, g i ∈ I) : c (dForm α fun i => h * g i) - h ^ D * c (dForm α g) ∈ I := by sorry
