-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_lineDerivCLM_apply_le
-- name    : GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_lineDerivCLM_apply_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:41.477662+00:00
-- url     : https://prove2.me/theorems/cc81d372-6f3e-4cc6-b33b-f26189929d91
-- title:
--   Sobolev Space: norm line Deriv CLM apply le
-- statement:
--   The Sobolev Space construction uses the norm line Deriv CLM apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L566-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L566-L568

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
variable {s : ℝ}

theorem GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_lineDerivCLM_apply_le (v : E) (u : SobolevSpace E F s) :
    ‖lineDerivCLM v u‖ ≤ 2 * Real.pi * ‖v‖ * ‖u‖ := by sorry
