-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_continuous_one_add_norm_sq_rpow
-- name    : GroundTheory.Automorphic.Sobolev.continuous_one_add_norm_sq_rpow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:50:41.941677+00:00
-- url     : https://prove2.me/theorems/81a93848-779e-4dc4-8915-af334139c78d
-- title:
--   Sobolev: continuous one add norm sq rpow
-- statement:
--   The Sobolev construction uses the continuous one add norm sq rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L192-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L192-L194

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

theorem GroundTheory.Automorphic.Sobolev.continuous_one_add_norm_sq_rpow (c : ℝ) : Continuous fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ c := by sorry
