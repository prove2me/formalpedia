-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_lineDerivOp_smulLeftCLM
-- name    : GroundTheory.Automorphic.Sobolev.lineDerivOp_smulLeftCLM
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:21.948866+00:00
-- url     : https://prove2.me/theorems/230d880f-13d0-436d-99e4-e95a72557432
-- title:
--   Sobolev: line Deriv Op smul Left CLM
-- statement:
--   The Sobolev construction uses the line Deriv Op smul Left CLM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L225-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L225-L231

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

theorem GroundTheory.Automorphic.Sobolev.lineDerivOp_smulLeftCLM (v : E) (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) :
    ∂_{v} (smulLeftCLM ℂ (ψ : E → ℂ) u) =
      smulLeftCLM ℂ ((∂_{v} ψ : 𝓢(E, ℂ)) : E → ℂ) u + smulLeftCLM ℂ (ψ : E → ℂ) (∂_{v} u) := by sorry
