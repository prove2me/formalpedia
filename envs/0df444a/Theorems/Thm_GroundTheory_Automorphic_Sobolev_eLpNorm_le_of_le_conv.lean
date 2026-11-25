-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_eLpNorm_le_of_le_conv
-- name    : GroundTheory.Automorphic.Sobolev.eLpNorm_le_of_le_conv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:50:21.450196+00:00
-- url     : https://prove2.me/theorems/fac50129-d466-56d2-bd8b-bd2d741578be
-- title:
--   Sobolev: e Lp Norm le of le conv
-- statement:
--   The Sobolev construction uses the e Lp Norm le of le conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L49-L57

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

theorem GroundTheory.Automorphic.Sobolev.eLpNorm_le_of_le_conv {h g : E → ℂ} {K : E → ℝ≥0∞} (hK : Measurable K)
    (hg : Measurable g) (hh : ∀ ξ, ‖h ξ‖ₑ ≤ ∫⁻ η, K (ξ - η) * ‖g η‖ₑ) :
    eLpNorm h 2 volume ≤ (∫⁻ ζ, K ζ) * eLpNorm g 2 volume := by sorry
