-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_eLpNorm_weight_fourier_lt_top
-- name    : GroundTheory.Automorphic.Sobolev.eLpNorm_weight_fourier_lt_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:49:59.279744+00:00
-- url     : https://prove2.me/theorems/a2770828-6c94-4677-98c8-9f8881c8fdd6
-- title:
--   Sobolev: e Lp Norm weight fourier lt top
-- statement:
--   The Sobolev construction uses the e Lp Norm weight fourier lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L121-L127

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

theorem GroundTheory.Automorphic.Sobolev.eLpNorm_weight_fourier_lt_top (r : ℝ) (φ : 𝓢(E, ℂ)) :
    eLpNorm (fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume < (⊤ : ℝ≥0∞) := by sorry
