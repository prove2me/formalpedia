-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_ofSchwartz_smulLeft_le
-- name    : GroundTheory.Automorphic.Sobolev.norm_ofSchwartz_smulLeft_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:43.301885+00:00
-- url     : https://prove2.me/theorems/1e7fa1f5-7788-42ad-a640-677f06a44590
-- title:
--   Sobolev: norm of Schwartz smul Left le
-- statement:
--   The Sobolev construction uses the norm of Schwartz smul Left le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L248-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L248-L261

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

theorem GroundTheory.Automorphic.Sobolev.norm_ofSchwartz_smulLeft_le (r : ℝ) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz r (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ)‖ ≤
      2 ^ (|r| / 2) * wInt (|r| / 2) (𝓕 χ) * ‖SobolevSpace.ofSchwartz r φ‖ := by sorry
