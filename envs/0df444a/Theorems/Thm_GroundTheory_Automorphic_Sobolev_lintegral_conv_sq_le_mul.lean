-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_lintegral_conv_sq_le_mul
-- name    : GroundTheory.Automorphic.Sobolev.lintegral_conv_sq_le_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:14.165831+00:00
-- url     : https://prove2.me/theorems/59c242d3-09bf-5db6-80a8-aeb7383ad77e
-- title:
--   Sobolev: lintegral conv sq le mul
-- statement:
--   The Sobolev construction uses the lintegral conv sq le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L32-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L32-L47

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

theorem GroundTheory.Automorphic.Sobolev.lintegral_conv_sq_le_mul {K G : E → ℝ≥0∞} (hK : Measurable K) (hG : Measurable G) :
    ∫⁻ ξ, (∫⁻ η, K (ξ - η) * G η) ^ 2 ≤ (∫⁻ ζ, K ζ) ^ 2 * ∫⁻ η, G η ^ 2 := by sorry
