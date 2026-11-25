-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_lintegral_conv_sq_le
-- name    : GroundTheory.Automorphic.Sobolev.lintegral_conv_sq_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:14.504426+00:00
-- url     : https://prove2.me/theorems/59945123-d1e9-50c0-af58-94eb62dea578
-- title:
--   Sobolev: lintegral conv sq le
-- statement:
--   The Sobolev construction uses the lintegral conv sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L17-L30

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

theorem GroundTheory.Automorphic.Sobolev.lintegral_conv_sq_le {K G : E → ℝ≥0∞} (hK : Measurable K) (hG : Measurable G) (ξ : E) :
    (∫⁻ η, K (ξ - η) * G η) ^ 2 ≤ (∫⁻ ζ, K ζ) * ∫⁻ η, K (ξ - η) * G η ^ 2 := by sorry
