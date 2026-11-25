-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_eq_zero_of_isVanishingOn
-- name    : GroundTheory.Automorphic.Sobolev.smulLeftCLM_eq_zero_of_isVanishingOn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:45.277376+00:00
-- url     : https://prove2.me/theorems/9f112984-645e-49f0-b878-4f1091ce0ac5
-- title:
--   Sobolev: smul Left CLM eq zero of is Vanishing On
-- statement:
--   The Sobolev construction uses the smul Left CLM eq zero of is Vanishing On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L176-L183

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

theorem GroundTheory.Automorphic.Sobolev.smulLeftCLM_eq_zero_of_isVanishingOn {g : E → ℂ} (hg : g.HasTemperateGrowth)
    {u : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U) (hgU : tsupport g ⊆ U) :
    smulLeftCLM ℂ g u = 0 := by sorry
