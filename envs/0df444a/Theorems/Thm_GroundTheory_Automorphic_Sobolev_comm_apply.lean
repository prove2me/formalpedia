-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_apply
-- name    : GroundTheory.Automorphic.Sobolev.comm_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:17.957826+00:00
-- url     : https://prove2.me/theorems/e626eda3-cb45-55ea-80e0-ee980340e4fa
-- title:
--   Sobolev: comm apply
-- statement:
--   The Sobolev construction uses the comm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L236-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L236-L237

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

theorem GroundTheory.Automorphic.Sobolev.comm_apply (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) :
    comm T ψ u = T (smulLeftCLM ℂ (ψ : E → ℂ) u) - smulLeftCLM ℂ (ψ : E → ℂ) (T u) := by sorry
