-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulPrin_coe
-- name    : GroundTheory.Automorphic.Sobolev.mulPrin_coe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:50:49.31447+00:00
-- url     : https://prove2.me/theorems/66c9667f-3480-419a-ba5c-b2938e270775
-- title:
--   Sobolev: mul Prin coe
-- statement:
--   The Sobolev construction uses the mul Prin coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L541-L547
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L541-L547

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.mulPrin_coe (χ : 𝓢(E, ℂ)) (r : ℝ) (φ : 𝓢(E, ℂ)) :
    mulPrin χ r (φ : 𝓢'(E, ℂ)) =
      ((SchwartzMap.fourierMultiplierCLM ℂ (weight (-r)) (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ)
        (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ)) : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by sorry
