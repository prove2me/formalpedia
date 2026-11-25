-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_smulLeft
-- name    : GroundTheory.Automorphic.Sobolev.opBound_smulLeft
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:23.974406+00:00
-- url     : https://prove2.me/theorems/438e83ab-5c8d-4fc5-b0cd-9dcd4f302603
-- title:
--   Sobolev: op Bound smul Left
-- statement:
--   The Sobolev construction uses the op Bound smul Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L466-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L466-L468

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.opBound_smulLeft (χ : 𝓢(E, ℂ)) (s : ℝ) :
    OpBound (smulLeftCLM ℂ (χ : E → ℂ)) s s (mulConst s χ) := by sorry
