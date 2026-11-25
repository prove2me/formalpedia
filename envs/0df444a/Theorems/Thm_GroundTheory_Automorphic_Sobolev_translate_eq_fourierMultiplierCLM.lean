-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_translate_eq_fourierMultiplierCLM
-- name    : GroundTheory.Automorphic.Sobolev.translate_eq_fourierMultiplierCLM
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:56:06.811122+00:00
-- url     : https://prove2.me/theorems/5dee0063-292d-4d08-bcd6-ff7dfe3d9ee2
-- title:
--   Sobolev: translate eq fourier Multiplier CLM
-- statement:
--   The Sobolev construction uses the translate eq fourier Multiplier CLM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L77-L80

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
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

theorem GroundTheory.Automorphic.Sobolev.translate_eq_fourierMultiplierCLM (h : E) (u : 𝓢'(E, F)) :
    translate F h u = fourierMultiplierCLM F (expChar (-h)) u := by sorry
