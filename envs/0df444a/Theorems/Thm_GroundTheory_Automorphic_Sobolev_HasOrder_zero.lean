-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_zero
-- name    : GroundTheory.Automorphic.Sobolev.HasOrder.zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:02:35.57811+00:00
-- url     : https://prove2.me/theorems/5727d763-411d-49a6-86ca-882532bab8e4
-- title:
--   Has Order: zero
-- statement:
--   The Has Order construction uses the zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L59-L60

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
open GroundTheory.Automorphic.Sobolev.HasOrder
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {k k₁ k₂ : ℝ}

theorem GroundTheory.Automorphic.Sobolev.HasOrder.zero (k : ℝ) : HasOrder (0 : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) k := by sorry
