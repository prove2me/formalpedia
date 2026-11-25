-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_coe
-- name    : GroundTheory.Automorphic.Sobolev.smulLeftCLM_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:49:50.751673+00:00
-- url     : https://prove2.me/theorems/7f7cfd11-272a-58a5-8ca3-48dc680771f9
-- title:
--   Sobolev: smul Left CLM coe
-- statement:
--   The Sobolev construction uses the smul Left CLM coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L502-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L502-L511

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

theorem GroundTheory.Automorphic.Sobolev.smulLeftCLM_coe (χ : 𝓢(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    smulLeftCLM ℂ (χ : E → ℂ) (φ : 𝓢'(E, ℂ)) =
      ((SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by sorry
