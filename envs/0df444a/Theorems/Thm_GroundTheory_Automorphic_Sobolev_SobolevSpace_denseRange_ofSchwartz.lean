-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_denseRange_ofSchwartz
-- name    : GroundTheory.Automorphic.Sobolev.SobolevSpace.denseRange_ofSchwartz
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:28.800653+00:00
-- url     : https://prove2.me/theorems/9f18add4-32ab-4d9a-bd2c-416d88df0ff4
-- title:
--   Sobolev Space: dense Range of Schwartz
-- statement:
--   The Sobolev Space construction uses the dense Range of Schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L522-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L522-L529

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

theorem GroundTheory.Automorphic.Sobolev.SobolevSpace.denseRange_ofSchwartz : DenseRange (ofSchwartz (E := E) (F := F) s) := by sorry
