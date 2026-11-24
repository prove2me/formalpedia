-- Prove2me | Theorems.Thm_GlobalTheory_IsFreeAction_isFreeRingAction
-- name    : GlobalTheory.IsFreeAction.isFreeRingAction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:28:22.677738+00:00
-- url     : https://prove2.me/theorems/6645397c-4447-463e-9641-235e01b05442
-- title:
--   Is Free Action: is Free Ring Action
-- statement:
--   The Is Free Action construction uses the is Free Ring Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L622-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L622-L627

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}

theorem GlobalTheory.IsFreeAction.isFreeRingAction {ρ : G →* Aut X} (h : IsFreeAction ρ) {U : X.Opens}
    (hU : IsAffineOpen U) (hst : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) :
    letI := sectionsAction ρ U hst
    IsFreeRingAction G Γ(X, U) := by sorry
