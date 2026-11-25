-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_add
-- name    : GroundTheory.Automorphic.Sobolev.HasOrder.add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:34.135702+00:00
-- url     : https://prove2.me/theorems/a9c011bb-4a84-4ee2-8fd3-16dad0fd4aa5
-- title:
--   Has Order: add
-- statement:
--   The Has Order construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L38-L44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add

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

theorem GroundTheory.Automorphic.Sobolev.HasOrder.add (h₁ : HasOrder T₁ k) (h₂ : HasOrder T₂ k) : HasOrder (T₁ + T₂) k := by sorry
