-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
-- name    : GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:59.197564+00:00
-- url     : https://prove2.me/theorems/aea78226-322b-4bec-86f1-aeebe6b66765
-- title:
--   Sobolev Space: to Distribution line Deriv CLM
-- statement:
--   The Sobolev Space construction uses the to Distribution line Deriv CLM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L558-L564
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L558-L564

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
open LineDeriv

theorem GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM (v : E) (u : SobolevSpace E F s) :
    toDistribution (lineDerivCLM v u) = ∂_{v} (toDistribution u) := by sorry
