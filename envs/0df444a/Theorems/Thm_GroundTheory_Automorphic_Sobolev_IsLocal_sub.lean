-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sub
-- name    : GroundTheory.Automorphic.Sobolev.IsLocal.sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:00:27.007564+00:00
-- url     : https://prove2.me/theorems/5c138527-52e6-4aa6-a54c-e9db88202176
-- title:
--   Is Local: sub
-- statement:
--   The Is Local construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L144-L145

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
open GroundTheory.Automorphic.Sobolev.IsLocal
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}

theorem GroundTheory.Automorphic.Sobolev.IsLocal.sub (h₁ : IsLocal T₁) (h₂ : IsLocal T₂) : IsLocal (T₁ - T₂) := by sorry
