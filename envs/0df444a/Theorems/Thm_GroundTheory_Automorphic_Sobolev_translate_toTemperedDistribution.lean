-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_translate_toTemperedDistribution
-- name    : GroundTheory.Automorphic.Sobolev.translate_toTemperedDistribution
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:48.978178+00:00
-- url     : https://prove2.me/theorems/a5c5abde-eef5-5204-8aaf-686b552a3350
-- title:
--   Sobolev: translate to Tempered Distribution
-- statement:
--   The Sobolev construction uses the translate to Tempered Distribution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L82-L90

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

theorem GroundTheory.Automorphic.Sobolev.translate_toTemperedDistribution (h : E) (f : Lp F 2 (volume : Measure E)) (φ : 𝓢(E, ℂ)) :
    translate F h (f : 𝓢'(E, F)) φ = ∫ x, φ x • f (x - h) := by sorry
