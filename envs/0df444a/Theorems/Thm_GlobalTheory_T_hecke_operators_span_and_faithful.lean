-- Prove2me | Theorems.Thm_GlobalTheory_T_hecke_operators_span_and_faithful
-- name    : GlobalTheory.T.hecke_operators_span_and_faithful
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:45:47.61602+00:00
-- url     : https://prove2.me/theorems/7359b9e2-c58a-47fb-80a0-2dcb87583758
-- title:
--   T: hecke operators span and faithful
-- statement:
--   The T construction uses the hecke operators span and faithful property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithfulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithfulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hecke_operators_span_and_faithful : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by sorry
