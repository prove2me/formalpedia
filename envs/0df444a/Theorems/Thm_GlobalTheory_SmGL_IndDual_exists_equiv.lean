-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndDual_exists_equiv
-- name    : GlobalTheory.SmGL.IndDual.exists_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:16.912495+00:00
-- url     : https://prove2.me/theorems/85e0f058-9c68-4443-8719-9f361dad5469
-- title:
--   Ind Dual: exists equiv
-- statement:
--   The Ind Dual construction uses the exists equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L307-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L307-L327

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
variable [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G}
  (hK : IsCompact (K : Set G)) (σ : Representation ℂ P W) (τ : Representation ℂ P W')
  (B : W' →ₗ[ℂ] Module.Dual ℂ W)

theorem GlobalTheory.SmGL.IndDual.exists_equiv
    (hinv : ∀ g f' f, pair μ hK σ τ B (smInd P τ g f') (smInd P σ g f) = pair μ hK σ τ B f' f)
    (hi : Function.Injective (pair μ hK σ τ B))
    (hs : ∀ l ∈ smoothPart (smInd P σ).dual, l ∈ LinearMap.range (pair μ hK σ τ B)) :
    ∃ Φ : (smInd P τ).Equiv (contra (smInd P σ)), ∀ f' f,
      (Φ f' : Module.Dual ℂ (smoothPart (ind P σ))) f = ∫ x in (K : Set G), B (f'.1.1 x) (f.1.1 x) ∂μ := by sorry
