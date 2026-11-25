-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_smulLeft
-- name    : GroundTheory.Automorphic.Sobolev.memSobolev_smulLeft
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:51:07.955618+00:00
-- url     : https://prove2.me/theorems/e08237d7-81fc-4681-b7dd-8333067ad785
-- title:
--   Sobolev: mem Sobolev smul Left
-- statement:
--   The Sobolev construction uses the mem Sobolev smul Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L525-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L525-L528

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

theorem GroundTheory.Automorphic.Sobolev.memSobolev_smulLeft (χ : 𝓢(E, ℂ)) {r : ℝ} {u : 𝓢'(E, ℂ)} (hu : MemSobolev r 2 u) :
    MemSobolev r 2 (smulLeftCLM ℂ (χ : E → ℂ) u) := by sorry
