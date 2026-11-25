-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_smulLeft_comp
-- name    : GroundTheory.Automorphic.Sobolev.comm_smulLeft_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:59.626817+00:00
-- url     : https://prove2.me/theorems/11d78609-07cb-5686-b231-38ff4dfd5572
-- title:
--   Sobolev: comm smul Left comp
-- statement:
--   The Sobolev construction uses the comm smul Left comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L251-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L251-L256

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

theorem GroundTheory.Automorphic.Sobolev.comm_smulLeft_comp {g : E → ℂ} (hg : g.HasTemperateGrowth) (A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
    (ψ : 𝓢(E, ℂ)) : comm (smulLeftCLM ℂ g ∘L A) ψ = smulLeftCLM ℂ g ∘L comm A ψ := by sorry
