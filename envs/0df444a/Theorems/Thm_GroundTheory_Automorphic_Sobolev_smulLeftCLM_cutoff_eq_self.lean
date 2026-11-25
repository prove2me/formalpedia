-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_cutoff_eq_self
-- name    : GroundTheory.Automorphic.Sobolev.smulLeftCLM_cutoff_eq_self
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:28.228666+00:00
-- url     : https://prove2.me/theorems/5a9dadb9-6f00-4ca8-8f0d-320fd08b149c
-- title:
--   Sobolev: smul Left CLM cutoff eq self
-- statement:
--   The Sobolev construction uses the smul Left CLM cutoff eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L37-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L37-L57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem GroundTheory.Automorphic.Sobolev.smulLeftCLM_cutoff_eq_self {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
    {R : ℝ} (u : 𝓢'(E, F')) (hu : Distribution.IsVanishingOn u (Metric.closedBall (0 : E) R)ᶜ) :
    smulLeftCLM F' (cutoff R : E → ℂ) u = u := by sorry
