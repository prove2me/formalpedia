-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- name    : GroundTheory.Automorphic.Sobolev.dualEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:54.774606+00:00
-- url     : https://prove2.me/theorems/a41b2a8a-74b5-4f4d-909b-7e3ff0359ac7
-- title:
--   Sobolev: dual Equiv apply
-- statement:
--   The Sobolev construction uses the dual Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevDuality.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevDuality.lean#L89-L90

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
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
variable {s : ℝ}

theorem GroundTheory.Automorphic.Sobolev.dualEquiv_apply (v : SobolevSpace E ℂ (-s)) :
    dualEquiv v = dualPairing v := by sorry

attribute [defeq] GroundTheory.Automorphic.Sobolev.dualEquiv_apply
