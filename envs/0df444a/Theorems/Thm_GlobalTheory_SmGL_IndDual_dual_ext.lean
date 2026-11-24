-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndDual_dual_ext
-- name    : GlobalTheory.SmGL.IndDual.dual_ext
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:42.761494+00:00
-- url     : https://prove2.me/theorems/28a928e1-088b-4f1a-b03a-0c82a935b295
-- title:
--   Ind Dual: dual ext
-- statement:
--   The Ind Dual construction uses the dual ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L170-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L170-L177

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

theorem GlobalTheory.SmGL.IndDual.dual_ext {σ : Representation ℂ G W} (hσ : IsSmooth σ) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {l l' : Module.Dual ℂ W} (hl : ∀ h ∈ H, ∀ w, l (σ h w) = l w) (hl' : ∀ h ∈ H, ∀ w, l' (σ h w) = l' w)
    (h : ∀ w ∈ fixed σ H, l w = l' w) : l = l' := by sorry
