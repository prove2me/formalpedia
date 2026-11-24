-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_image_of_trivial_on_inf_finiteIndex
-- name    : GlobalTheory.T.finite_image_of_trivial_on_inf_finiteIndex
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:14.426465+00:00
-- url     : https://prove2.me/theorems/2fa9be9a-7256-4c3b-9eae-87194de6d0cd
-- title:
--   T: finite image of trivial on inf finite Index
-- statement:
--   The T construction uses the finite image of trivial on inf finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImageFiniteOfTrivialOnInfFiniteIndexStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImageFiniteOfTrivialOnInfFiniteIndexStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImageFiniteOfTrivialOnInfFiniteIndex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImageFiniteOfTrivialOnInfFiniteIndexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_image_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by sorry
