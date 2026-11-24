-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndDual_pair_bijective
-- name    : GlobalTheory.SmGL.IndDual.pair_bijective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:25.633113+00:00
-- url     : https://prove2.me/theorems/c9f4b502-8053-458d-9433-cd95e711f9a3
-- title:
--   Ind Dual: pair bijective
-- statement:
--   The Ind Dual construction uses the pair bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L226-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean#L226-L305

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

theorem GlobalTheory.SmGL.IndDual.pair_bijective (hKo : IsOpen (K : Set G)) (hP : IsClosed (P : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hσ : IsSmooth σ) (hB : ∀ p : P, (p : G) ∈ K → ∀ w' w, B (τ p w') (σ p w) = B w' w)
    (hBi : Function.Injective B)
    (hBs : ∀ l : Module.Dual ℂ W, (∀ᶠ p in 𝓝 (1 : P), ∀ w, l (σ p w) = l w) → l ∈ LinearMap.range B)
    (hinv : ∀ g f' f, pair μ hK σ τ B (smInd P τ g f') (smInd P σ g f) = pair μ hK σ τ B f' f) :
    Function.Injective (pair μ hK σ τ B) ∧
      ∀ l ∈ smoothPart (smInd P σ).dual, l ∈ LinearMap.range (pair μ hK σ τ B) := by sorry
