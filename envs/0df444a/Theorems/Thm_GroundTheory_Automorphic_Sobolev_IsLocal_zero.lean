-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_zero
-- name    : GroundTheory.Automorphic.Sobolev.IsLocal.zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:27.892194+00:00
-- url     : https://prove2.me/theorems/92a3312f-4ce6-4d52-aca9-2310d6e78bb9
-- title:
--   Is Local: zero
-- statement:
--   The Is Local construction uses the zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L153-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L153-L153

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

theorem GroundTheory.Automorphic.Sobolev.IsLocal.zero : IsLocal (0 : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) := by sorry
