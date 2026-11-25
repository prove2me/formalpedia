-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_smulLeft
-- name    : GroundTheory.Automorphic.Sobolev.hasOrder_smulLeft
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:00:22.832864+00:00
-- url     : https://prove2.me/theorems/7585e74d-3ba8-4cf4-a704-0bd1f1fbef1f
-- title:
--   Sobolev: has Order smul Left
-- statement:
--   The Sobolev construction uses the has Order smul Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L86-L88

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
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

theorem GroundTheory.Automorphic.Sobolev.hasOrder_smulLeft (χ : 𝓢(E, ℂ)) : HasOrder (smulLeftCLM ℂ (χ : E → ℂ)) 0 := by sorry
