-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_lintegral_wK
-- name    : GroundTheory.Automorphic.Sobolev.lintegral_wK
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:50:27.225235+00:00
-- url     : https://prove2.me/theorems/481f5adc-f1f8-58cd-907c-d2371552567f
-- title:
--   Sobolev: lintegral w K
-- statement:
--   The Sobolev construction uses the lintegral w K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L220-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L220-L223

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

theorem GroundTheory.Automorphic.Sobolev.lintegral_wK (c : ℝ) (ψ : 𝓢(E, ℂ)) : ∫⁻ ζ, wK c ψ ζ = ENNReal.ofReal (wInt c ψ) := by sorry
