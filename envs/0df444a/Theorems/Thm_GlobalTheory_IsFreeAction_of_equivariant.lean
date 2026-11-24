-- Prove2me | Theorems.Thm_GlobalTheory_IsFreeAction_of_equivariant
-- name    : GlobalTheory.IsFreeAction.of_equivariant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:09.802892+00:00
-- url     : https://prove2.me/theorems/2c62b645-94bf-4ecf-bd2e-6c9bae03a2ab
-- title:
--   Is Free Action: of equivariant
-- statement:
--   The Is Free Action construction uses the of equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L584-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L584-L586

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

theorem GlobalTheory.IsFreeAction.of_equivariant {ρ : G →* Aut X} (h : IsFreeAction ρ) {ρ' : G →* Aut Y}
    (p : Y ⟶ X) (hp : ∀ g, (ρ' g).hom ≫ p = p ≫ (ρ g).hom) : IsFreeAction ρ' := by sorry
