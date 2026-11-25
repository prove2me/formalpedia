-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_isVanishingOn_smulLeftCLM_sub
-- name    : GroundTheory.Automorphic.Sobolev.isVanishingOn_smulLeftCLM_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:30.7618+00:00
-- url     : https://prove2.me/theorems/85e0e91d-ccb2-407a-ae8a-d42dc894c906
-- title:
--   Sobolev: is Vanishing On smul Left CLM sub
-- statement:
--   The Sobolev construction uses the is Vanishing On smul Left CLM sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L185-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L185-L195

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

theorem GroundTheory.Automorphic.Sobolev.isVanishingOn_smulLeftCLM_sub {g : E → ℂ} (hg : g.HasTemperateGrowth) {V : Set E}
    (hgV : ∀ x ∈ V, g x = 1) (u : 𝓢'(E, ℂ)) :
    Distribution.IsVanishingOn (smulLeftCLM ℂ g u - u) V := by sorry
