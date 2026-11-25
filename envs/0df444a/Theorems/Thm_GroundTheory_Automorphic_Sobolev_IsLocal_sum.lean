-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sum
-- name    : GroundTheory.Automorphic.Sobolev.IsLocal.sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:50.285408+00:00
-- url     : https://prove2.me/theorems/c13f94f8-5598-457f-8ed5-4e06071f24e5
-- title:
--   Is Local: sum
-- statement:
--   The Is Local construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L157-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L157-L164

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
open GroundTheory.Automorphic.Sobolev.IsLocal
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}

theorem GroundTheory.Automorphic.Sobolev.IsLocal.sum {ι : Type*} (S : Finset ι) {T : ι → 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
    (h : ∀ i ∈ S, IsLocal (T i)) : IsLocal (∑ i ∈ S, T i) := by sorry
