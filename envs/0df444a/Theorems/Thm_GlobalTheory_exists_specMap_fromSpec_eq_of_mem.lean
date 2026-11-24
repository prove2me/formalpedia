-- Prove2me | Theorems.Thm_GlobalTheory_exists_specMap_fromSpec_eq_of_mem
-- name    : GlobalTheory.exists_specMap_fromSpec_eq_of_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:28:20.488851+00:00
-- url     : https://prove2.me/theorems/08d97750-f03c-4b47-8812-36700d343917
-- title:
--   Global Theory: exists spec Map from Spec eq of mem
-- statement:
--   The Global Theory construction uses the exists spec Map from Spec eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L827-L833
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsDomainAndIsIntegrallyClosedLocalizationOfIsInv.lean#L827-L833

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
open GlobalTheory.IsAffineQuotient
variable {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} {ρ : G →* Aut X} {π : X ⟶ Y}
  (h : IsAffineQuotient ρ π) {k : Type u} [Field k]

theorem GlobalTheory.exists_specMap_fromSpec_eq_of_mem (x : Spec (.of k) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (hx : x default ∈ U) :
    ∃ φ : Γ(X, U) ⟶ .of k, Spec.map φ ≫ hU.fromSpec = x := by sorry
