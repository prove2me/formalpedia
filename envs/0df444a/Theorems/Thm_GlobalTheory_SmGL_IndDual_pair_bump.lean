-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndDual_pair_bump
-- name    : GlobalTheory.SmGL.IndDual.pair_bump
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:35.980104+00:00
-- url     : https://prove2.me/theorems/e1de81e3-8007-4626-bf41-1aa029ab35ad
-- title:
--   Ind Dual: pair bump
-- statement:
--   The Ind Dual construction uses the pair bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L204-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L204-L217

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

theorem GlobalTheory.SmGL.IndDual.pair_bump (hB : ∀ p : P, (p : G) ∈ K → ∀ w' w, B (τ p w') (σ p w) = B w' w)
    {J : Subgroup G} (hJ : IsOpen (J : Set G)) (hle : J ≤ K) (f' : smoothPart (ind P τ))
    (hf : ∀ j ∈ J, f'.1.1 j = f'.1.1 1) (w : fixed σ (J.subgroupOf P)) :
    pair μ hK σ τ B f' (bump σ hJ w) = (μ.real (K ∩ cell P J) : ℂ) * B (f'.1.1 1) w := by sorry
