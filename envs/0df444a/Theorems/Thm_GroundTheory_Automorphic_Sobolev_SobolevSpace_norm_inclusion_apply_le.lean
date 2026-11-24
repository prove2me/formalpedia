-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_inclusion_apply_le
-- name    : GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_inclusion_apply_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:36.836185+00:00
-- url     : https://prove2.me/theorems/724201ce-5180-4cff-b658-4eb4e78ab045
-- title:
--   Sobolev Space: norm inclusion apply le
-- statement:
--   The Sobolev Space construction uses the norm inclusion apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L492-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L492-L497

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
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
variable {m : E → ℂ} {C s t : ℝ}
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s t : ℝ}

theorem GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_inclusion_apply_le (h : t ≤ s) (u : SobolevSpace E F s) :
    ‖inclusion h u‖ ≤ ‖u‖ := by sorry
