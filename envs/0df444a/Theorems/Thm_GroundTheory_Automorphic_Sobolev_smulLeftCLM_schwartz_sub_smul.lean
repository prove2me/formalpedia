-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_schwartz_sub_smul
-- name    : GroundTheory.Automorphic.Sobolev.smulLeftCLM_schwartz_sub_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:33.685803+00:00
-- url     : https://prove2.me/theorems/314ae81d-0b87-5117-bcf2-6a6d52af2b68
-- title:
--   Sobolev: smul Left CLM schwartz sub smul
-- statement:
--   The Sobolev construction uses the smul Left CLM schwartz sub smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L352-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L352-L363

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
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

theorem GroundTheory.Automorphic.Sobolev.smulLeftCLM_schwartz_sub_smul (f g : 𝓢(E, ℂ)) (c : ℂ) (v : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ ((f - c • g : 𝓢(E, ℂ)) : E → ℂ) v =
      smulLeftCLM ℂ (f : E → ℂ) v - c • smulLeftCLM ℂ (g : E → ℂ) v := by sorry
