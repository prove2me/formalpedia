-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_weight_sub_weight
-- name    : GroundTheory.Automorphic.Sobolev.norm_weight_sub_weight
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:07.411987+00:00
-- url     : https://prove2.me/theorems/fa5b1028-614b-5a22-be73-1a766417325f
-- title:
--   Sobolev: norm weight sub weight
-- statement:
--   The Sobolev construction uses the norm weight sub weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L296-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L296-L299

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

theorem GroundTheory.Automorphic.Sobolev.norm_weight_sub_weight (r : ℝ) (ξ η : E) :
    ‖weight r ξ - weight r η‖ = |(1 + ‖ξ‖ ^ 2) ^ (r / 2) - (1 + ‖η‖ ^ 2) ^ (r / 2)| := by sorry
