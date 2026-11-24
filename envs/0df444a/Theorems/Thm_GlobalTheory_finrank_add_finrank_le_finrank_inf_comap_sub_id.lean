-- Prove2me | Theorems.Thm_GlobalTheory_finrank_add_finrank_le_finrank_inf_comap_sub_id
-- name    : GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:47:09.166934+00:00
-- url     : https://prove2.me/theorems/8d942828-453e-49ed-ac04-1a5a8f38fd55
-- title:
--   Global Theory: finrank add finrank le finrank inf comap sub id
-- statement:
--   The Global Theory construction uses the finrank add finrank le finrank inf comap sub id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAddFinrankLeFinrankInfComapSubId.lean#L7-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAddFinrankLeFinrankInfComapSubId.lean#L7-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddFinrankLeFinrankInfComapSubId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory

theorem GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id :
    ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by sorry
