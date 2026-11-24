-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndDual_mem_span_bump
-- name    : GlobalTheory.SmGL.IndDual.mem_span_bump
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:37.534272+00:00
-- url     : https://prove2.me/theorems/c3cb636d-e610-4ffe-add8-2f071b2fa157
-- title:
--   Ind Dual: mem span bump
-- statement:
--   The Ind Dual construction uses the mem span bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L123-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L123-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W'] {P : Subgroup G}

theorem GlobalTheory.SmGL.IndDual.mem_span_bump (σ : Representation ℂ P W) {J K : Subgroup G} (hJ : IsOpen (J : Set G))
    (hK : IsCompact (K : Set G)) (hle : J ≤ K) (hn : ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x) (f : smoothPart (ind P σ))
    (hf : ∀ j ∈ J, smInd P σ j f = f) :
    f ∈ Submodule.span ℂ {v | ∃ z ∈ K, ∃ w, v = smInd P σ z⁻¹ (bump σ hJ w)} := by sorry
