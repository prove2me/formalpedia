-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_lineDeriv
-- name    : GroundTheory.Automorphic.Sobolev.hasOrder_lineDeriv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:42.179586+00:00
-- url     : https://prove2.me/theorems/d406c337-2397-5db5-9fd5-0f399a5b1c6f
-- title:
--   Sobolev: has Order line Deriv
-- statement:
--   The Sobolev construction uses the has Order line Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L96-L97

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

theorem GroundTheory.Automorphic.Sobolev.hasOrder_lineDeriv (v : E) : HasOrder (lineDerivOpCLM ℂ 𝓢'(E, ℂ) v) 1 := by sorry
