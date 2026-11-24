-- Prove2me | Theorems.Thm_GlobalTheory_image_finite_of_trivial_on_inf_finiteIndex
-- name    : GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:03.158911+00:00
-- url     : https://prove2.me/theorems/5b931209-87d3-4301-bd66-07b0f43be632
-- title:
--   Global Theory: image finite of trivial on inf finite Index
-- statement:
--   The Global Theory construction uses the image finite of trivial on inf finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImageFiniteOfTrivialOnInfFiniteIndex.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImageFiniteOfTrivialOnInfFiniteIndex.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImageFiniteOfTrivialOnInfFiniteIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by sorry
