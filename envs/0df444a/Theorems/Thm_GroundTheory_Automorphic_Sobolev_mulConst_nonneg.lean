-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulConst_nonneg
-- name    : GroundTheory.Automorphic.Sobolev.mulConst_nonneg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:11.875682+00:00
-- url     : https://prove2.me/theorems/f2078943-8c2d-466a-b791-bbc99f4ba85f
-- title:
--   Sobolev: mul Const nonneg
-- statement:
--   The Sobolev construction uses the mul Const nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L515-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L515-L516

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

theorem GroundTheory.Automorphic.Sobolev.mulConst_nonneg (r : ℝ) (χ : 𝓢(E, ℂ)) : 0 ≤ mulConst r χ := by sorry
