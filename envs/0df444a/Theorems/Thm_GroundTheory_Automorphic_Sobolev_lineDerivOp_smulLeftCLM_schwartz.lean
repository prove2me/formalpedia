-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_lineDerivOp_smulLeftCLM_schwartz
-- name    : GroundTheory.Automorphic.Sobolev.lineDerivOp_smulLeftCLM_schwartz
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:42.050275+00:00
-- url     : https://prove2.me/theorems/19cb8fcc-4854-4a60-9af3-3859729c5f4a
-- title:
--   Sobolev: line Deriv Op smul Left CLM schwartz
-- statement:
--   The Sobolev construction uses the line Deriv Op smul Left CLM schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L209-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L209-L223

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

theorem GroundTheory.Automorphic.Sobolev.lineDerivOp_smulLeftCLM_schwartz (v : E) (ψ φ : 𝓢(E, ℂ)) :
    ∂_{v} (SchwartzMap.smulLeftCLM ℂ (ψ : E → ℂ) φ) =
      SchwartzMap.smulLeftCLM ℂ ((∂_{v} ψ : 𝓢(E, ℂ)) : E → ℂ) φ +
        SchwartzMap.smulLeftCLM ℂ (ψ : E → ℂ) (∂_{v} φ) := by sorry
