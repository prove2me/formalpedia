-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
-- name    : GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:07.342424+00:00
-- url     : https://prove2.me/theorems/341f8b58-cbcb-4172-a4d2-566688dff1bb
-- title:
--   Sobolev Space: to Distribution convolution CLM
-- statement:
--   The Sobolev Space construction uses the to Distribution convolution CLM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L170-L172

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}

theorem GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM (ψ : 𝓢(E, ℂ)) (u : SobolevSpace E F s) :
    toDistribution (convolutionCLM ψ u) = convolution F ψ (toDistribution u) := by sorry
