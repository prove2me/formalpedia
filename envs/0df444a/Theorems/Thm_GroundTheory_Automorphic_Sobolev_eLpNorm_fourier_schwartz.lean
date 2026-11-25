-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_eLpNorm_fourier_schwartz
-- name    : GroundTheory.Automorphic.Sobolev.eLpNorm_fourier_schwartz
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:50:14.777807+00:00
-- url     : https://prove2.me/theorems/174b43aa-87cc-5926-b5f3-689d4cbe8385
-- title:
--   Sobolev: e Lp Norm fourier schwartz
-- statement:
--   The Sobolev construction uses the e Lp Norm fourier schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L98-L104

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

theorem GroundTheory.Automorphic.Sobolev.eLpNorm_fourier_schwartz (f : 𝓢(E, ℂ)) :
    eLpNorm (𝓕 f : 𝓢(E, ℂ)) 2 volume = eLpNorm f 2 volume := by sorry
